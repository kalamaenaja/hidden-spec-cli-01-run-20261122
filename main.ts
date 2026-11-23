// main.ts is mend, the CLI SPEC.md specifies. It implements every section of SPEC.md: the command line (1), the output
// and exit codes (2), safe paths (3), format detection (4), three-tier line matching (5), unified diffs (6),
// SEARCH/REPLACE blocks (7), V4A patches (8), tool-call JSON (9) and the all-or-nothing write (10).
// Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file split into lines, keeping its line break and whether it ends with one (SPEC.md section 3). */
interface FileLines {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileLines {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { lines: parts, br, final };
}

function joinFile(f: FileLines): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/* ------------------------------------------------------------------ section 5: matching */

const trimEndWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndWs(a) === trimEndWs(b);
  return trimWs(a) === trimWs(b);
}

/** All positions at or after `from` where O occurs at the given tier. */
function occurrences(lines: string[], o: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0..2, or only 0 when strict) with an occurrence at or after `from`. */
function findTier(lines: string[], o: string[], strict: boolean, from = 0): { tier: number; pos: number[] } | null {
  const max = strict ? 0 : 2;
  for (let t = 0; t <= max; t++) {
    const pos = occurrences(lines, o, t, from);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** A line of N: a context line is written as the file's own matched line, an added line as itself. */
interface NewLine {
  text: string;
  ctx: number | null;
}

const leadOf = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

/** At tier 2, an added non-blank line that starts with O's indent takes the file's indent instead. */
function reindent(text: string, f: string, p: string): string {
  if (text === '' || text.trim() === '') return text;
  return text.startsWith(p) ? f + text.slice(p.length) : text;
}

/** Replace the O lines at `at` with the N lines, keeping the rest of the file.
 *  SPEC.md section 5: at tier 2 only, a non-blank added line that starts with
 *  O's first-line indent P is re-indented to the file's first matched line
 *  indent F; at tiers 0 and 1 every added line is written as it is. A context
 *  line is always the file's own matched line, never the patch's text. */
function applyReplacement(fileLines: string[], at: number, o: string[], n: NewLine[], tier: number): string[] {
  const out = fileLines.slice(0, at);
  if (o.length > 0) {
    const f = leadOf(fileLines[at]!);
    const p = leadOf(o[0]!);
    for (const nl of n) {
      if (nl.ctx !== null) out.push(fileLines[at + nl.ctx]!);
      else if (tier === 2) out.push(reindent(nl.text, f, p));
      else out.push(nl.text);
    }
  } else {
    for (const nl of n) out.push(nl.text);
  }
  out.push(...fileLines.slice(at + o.length));
  return out;
}

/* ------------------------------------------------------------------ section 6: unified diff */

interface BodyItem {
  kind: ' ' | '-' | '+';
  text: string;
  backslash: boolean;
}

interface Hunk {
  a: number;
  body: BodyItem[];
  o: string[];
  n: NewLine[];
  lastNBackslash: boolean;
}

interface Section {
  oldFrom: string | null;
  newTo: string | null;
  headerOld: string | null;
  headerNew: string | null;
  diffOld: string | null;
  diffNew: string | null;
  pairSet: boolean;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

/** The path a `--- ` or `+++ ` header line names, or null for `/dev/null`. */
function headerPath(line: string): string | null {
  const after = line.slice(4);
  const tab = after.indexOf('\t');
  const raw = (tab < 0 ? after : after.slice(0, tab)).trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

function newSection(diffOld: string | null, diffNew: string | null): Section {
  return {
    oldFrom: null,
    newTo: null,
    headerOld: null,
    headerNew: null,
    diffOld,
    diffNew,
    pairSet: false,
    isCreate: false,
    isDelete: false,
    hunks: [],
  };
}

function parseUnified(lines: string[]): Section[] {
  const sections: Section[] = [];
  let sec: Section | null = null;
  let hunk: Hunk | null = null;
  let inHeader = false;
  let bodyClosed = false;

  const closeHunk = (): void => {
    if (hunk === null || sec === null) return;
    // SPEC.md section 6: empty lines at the end of a body are not part of it,
    // so trailing empty context lines are dropped before O and N are built.
    while (hunk.body.length > 0) {
      const last = hunk.body[hunk.body.length - 1]!;
      if (last.kind === ' ' && last.text === '' && !last.backslash) hunk.body.pop();
      else break;
    }
    const o: string[] = [];
    const n: NewLine[] = [];
    let lastNBackslash = false;
    for (const item of hunk.body) {
      if (item.kind === ' ' || item.kind === '-') {
        if (item.kind === ' ') n.push({ text: item.text, ctx: o.length });
        o.push(item.text);
      } else {
        n.push({ text: item.text, ctx: null });
      }
      if (item.kind === ' ' || item.kind === '+') lastNBackslash = item.backslash;
    }
    hunk.o = o;
    hunk.n = n;
    hunk.lastNBackslash = lastNBackslash;
    sec.hunks.push(hunk);
    hunk = null;
  };

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      closeHunk();
      sec = newSection(m[1]!, m[2]!);
      sections.push(sec);
      inHeader = true;
      bodyClosed = false;
      continue;
    }
    if (line.startsWith('--- ')) {
      const nxt = lines[i + 1];
      if (nxt !== undefined && nxt.startsWith('+++ ')) {
        if (sec !== null && inHeader && !sec.pairSet) {
          sec.headerOld = headerPath(line);
          sec.headerNew = headerPath(nxt);
          sec.pairSet = true;
          i++;
          continue;
        }
        closeHunk();
        sec = newSection(null, null);
        sec.headerOld = headerPath(line);
        sec.headerNew = headerPath(nxt);
        sec.pairSet = true;
        sections.push(sec);
        inHeader = true;
        bodyClosed = false;
        i++;
        continue;
      }
      if (sec !== null && inHeader) throw new Exit2(`error: parse ${i + 2}`);
      closeHunk();
      bodyClosed = true;
      continue;
    }
    if (line.startsWith('+++ ')) {
      closeHunk();
      bodyClosed = true;
      continue;
    }
    if (sec !== null && inHeader) {
      if (line.startsWith('rename from ')) {
        if (sec.oldFrom === null) sec.oldFrom = line.slice('rename from '.length).trim();
        continue;
      }
      if (line.startsWith('rename to ')) {
        if (sec.newTo === null) sec.newTo = line.slice('rename to '.length).trim();
        continue;
      }
      if (line === 'new file mode' || line.startsWith('new file mode ')) {
        sec.isCreate = true;
        continue;
      }
      if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
        sec.isDelete = true;
        continue;
      }
    }
    if (line.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      if (sec === null) throw new Exit2(`error: parse ${i + 1}`);
      closeHunk();
      hunk = { a: Number(m[1]), body: [], o: [], n: [], lastNBackslash: false };
      inHeader = false;
      bodyClosed = false;
      continue;
    }
    if (hunk !== null && !bodyClosed) {
      const c = line[0];
      if (c === ' ' || c === '-' || c === '+') {
        hunk.body.push({ kind: c, text: line.slice(1), backslash: false });
        continue;
      }
      if (c === '\\') {
        const last = hunk.body[hunk.body.length - 1];
        if (last !== undefined) last.backslash = true;
        continue;
      }
      if (line === '') {
        hunk.body.push({ kind: ' ', text: '', backslash: false });
        continue;
      }
      closeHunk();
      bodyClosed = true;
      continue;
    }
    // Outside bodies, lines that are not part of a section header are ignored.
  }
  closeHunk();
  return sections;
}

/** Apply a section's hunks to a file, in order, tracking the offset they introduce. */
function applyHunks(file: FileLines, hunks: Hunk[], strict: boolean, path: string): FileLines {
  let lines = file.lines.slice();
  let final = file.final;
  let d = 0;
  for (const h of hunks) {
    const o = h.o;
    const n = h.n;
    if (o.length === 0) {
      const at = Math.min(h.a + d, lines.length);
      const wasEnd = at === lines.length;
      lines.splice(at, 0, ...n.map((x) => x.text));
      if (wasEnd) final = !h.lastNBackslash;
      d += n.length;
      continue;
    }
    const found = findTier(lines, o, strict);
    if (found === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.pos[0]!;
    let bestDist = Math.abs(best - target);
    for (const p of found.pos) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const touchedEnd = best + o.length === lines.length;
    lines = applyReplacement(lines, best, o, n, found.tier);
    if (touchedEnd) final = !h.lastNBackslash;
    d += n.length - o.length;
  }
  return { lines, br: file.br, final };
}

function unifiedEdits(sections: Section[], strict: boolean): Edit[] {
  return sections.map((sec) => (tree: Tree): void => {
    const oldP = sec.headerOld ?? sec.oldFrom ?? sec.diffOld;
    const newP = sec.headerNew ?? sec.newTo ?? sec.diffNew;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    if (sec.isCreate || oldP === null) {
      if (newP === null) return;
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const outLines: string[] = [];
      let lastPlusBackslash = false;
      for (const h of sec.hunks) {
        for (const item of h.body) {
          if (item.kind === '+') {
            outLines.push(item.text);
            lastPlusBackslash = item.backslash;
          }
        }
      }
      tree.now.set(newP, outLines.length === 0 ? '' : outLines.join('\n') + (lastPlusBackslash ? '' : '\n'));
      return;
    }
    if (sec.isDelete || newP === null) {
      const op = oldP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    if (oldP !== newP) {
      const op = oldP!;
      const np = newP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const result = applyHunks(splitFile(tree.get(op)!), sec.hunks, strict, op);
      tree.now.set(op, null);
      tree.now.set(np, joinFile(result));
      tree.moves.push([op, np]);
      return;
    }
    const op = oldP!;
    if (tree.get(op) === null) throw new Fail('missing', op);
    const result = applyHunks(splitFile(tree.get(op)!), sec.hunks, strict, op);
    tree.now.set(op, joinFile(result));
  });
}

/* ------------------------------------------------------------------ section 7: SEARCH/REPLACE */

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree: Tree): void => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    const f = splitFile(cur);
    const found = findTier(f.lines, oldLines, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.pos.length > 1) throw new Fail('ambiguous', path);
    const n: NewLine[] = newLines.map((t) => ({ text: t, ctx: null }));
    f.lines = applyReplacement(f.lines, found.pos[0]!, oldLines, n, found.tier);
    tree.now.set(path, joinFile(f));
  };
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    const si = lines.findIndex((l, idx) => idx >= i && l.trimEnd() === '<<<<<<< SEARCH');
    if (si < 0) break;
    const eq = lines.findIndex((l, idx) => idx > si && l.trimEnd() === '=======');
    const rep = eq < 0 ? -1 : lines.findIndex((l, idx) => idx > eq && l.trimEnd() === '>>>>>>> REPLACE');
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${si + 1}`);
    let path: string | null = null;
    for (let j = si - 1; j > prevEnd; j--) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${si + 1}`);
      path = prevPath;
    }
    edits.push(srEdit(path, lines.slice(si + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ section 8: V4A */

interface V4aChunk {
  anchor: string | null;
  body: BodyItem[];
  o: string[];
  n: NewLine[];
  eof: boolean;
}

const SECTION_START = /^\*\*\* (Add File|Delete File|Update File): /;

/** A section's raw lines (trailing blank lines stripped) and the index where it ends. */
function collectV4aSection(lines: string[], start: number, last: number): { body: string[]; end: number } {
  let end = start;
  while (end < last) {
    if (SECTION_START.test(lines[end]!)) break;
    end++;
  }
  const body = lines.slice(start, end);
  while (body.length > 0 && blank(body[body.length - 1]!)) body.pop();
  return { body, end };
}

function v4aAdd(path: string, fileLines: string[]): Edit {
  return (tree: Tree): void => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
  };
}

function v4aDelete(path: string): Edit {
  return (tree: Tree): void => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}

function applyV4aChunks(file: FileLines, chunks: V4aChunk[], strict: boolean, path: string): FileLines {
  let lines = file.lines.slice();
  let cursor = 0;
  for (const ch of chunks) {
    if (ch.anchor !== null) {
      const found = findTier(lines, [ch.anchor], strict, cursor);
      if (found === null) throw new Fail('no-match', path);
      cursor = found.pos[0]! + 1;
    }
    const o = ch.o;
    const n = ch.n;
    if (o.length === 0) {
      const at = ch.eof ? lines.length : cursor;
      lines.splice(at, 0, ...n.map((x) => x.text));
      cursor = at + n.length;
      continue;
    }
    const found = findTier(lines, o, strict, cursor);
    if (found === null) throw new Fail('no-match', path);
    let at: number | null = null;
    for (const p of found.pos) {
      if (ch.eof) {
        if (p + o.length === lines.length) {
          at = p;
          break;
        }
      } else {
        at = p;
        break;
      }
    }
    if (at === null) throw new Fail('no-match', path);
    lines = applyReplacement(lines, at, o, n, found.tier);
    cursor = at + n.length;
  }
  return { lines, br: file.br, final: file.final };
}

function v4aUpdate(path: string, body: string[], updateIdx: number, strict: boolean): Edit {
  let moveTo: string | null = null;
  let rest = body;
  if (rest.length > 0 && rest[0]!.startsWith('*** Move to: ')) {
    moveTo = rest[0]!.slice('*** Move to: '.length).trim();
    rest = rest.slice(1);
  }
  const base = updateIdx + 2 + (body.length - rest.length);
  const chunks: V4aChunk[] = [];
  let cur: V4aChunk | null = null;
  let afterEof = false;
  let sawChunk = false;
  const closeChunk = (): void => {
    if (cur === null) return;
    const o: string[] = [];
    const n: NewLine[] = [];
    for (const item of cur.body) {
      if (item.kind === ' ' || item.kind === '-') {
        if (item.kind === ' ') n.push({ text: item.text, ctx: o.length });
        o.push(item.text);
      } else {
        n.push({ text: item.text, ctx: null });
      }
    }
    cur.o = o;
    cur.n = n;
    chunks.push(cur);
    cur = null;
  };
  for (let k = 0; k < rest.length; k++) {
    const l = rest[k]!;
    const lineNo = base + k;
    if (l.startsWith('@@')) {
      closeChunk();
      const anchor = l.slice(2).trim();
      cur = { anchor: anchor === '' ? null : anchor, body: [], o: [], n: [], eof: false };
      sawChunk = true;
      afterEof = false;
      continue;
    }
    if (l === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${lineNo}`);
      cur.eof = true;
      closeChunk();
      afterEof = true;
      continue;
    }
    if (l === '') {
      if (afterEof) throw new Exit2(`error: parse ${lineNo}`);
      if (cur === null) {
        if (sawChunk) throw new Exit2(`error: parse ${lineNo}`);
        cur = { anchor: null, body: [], o: [], n: [], eof: false };
        sawChunk = true;
      }
      cur.body.push({ kind: ' ', text: '', backslash: false });
      continue;
    }
    const c = l[0]!;
    if (c === ' ' || c === '-' || c === '+') {
      if (afterEof) throw new Exit2(`error: parse ${lineNo}`);
      if (cur === null) {
        if (sawChunk) throw new Exit2(`error: parse ${lineNo}`);
        cur = { anchor: null, body: [], o: [], n: [], eof: false };
        sawChunk = true;
      }
      cur.body.push({ kind: c, text: l.slice(1), backslash: false });
      continue;
    }
    throw new Exit2(`error: parse ${lineNo}`);
  }
  closeChunk();
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateIdx + 1}`);
  return (tree: Tree): void => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const result = applyV4aChunks(splitFile(cur), chunks, strict, path);
    const text = joinFile(result);
    if (moveTo !== null) {
      tree.now.set(path, null);
      tree.now.set(moveTo, text);
      tree.moves.push([path, moveTo]);
    } else {
      tree.now.set(path, text);
    }
  };
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    let m: RegExpExecArray | null;
    if ((m = /^\*\*\* Add File: (.*)$/.exec(line)) !== null) {
      const path = m[1]!.trim();
      const { body, end } = collectV4aSection(lines, i + 1, last);
      const fileLines: string[] = [];
      for (let k = 0; k < body.length; k++) {
        const bl = body[k]!;
        if (bl === '') fileLines.push('');
        else if (bl.startsWith('+')) fileLines.push(bl.slice(1));
        else throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(v4aAdd(path, fileLines));
      i = end;
      continue;
    }
    if ((m = /^\*\*\* Delete File: (.*)$/.exec(line)) !== null) {
      const path = m[1]!.trim();
      const { body, end } = collectV4aSection(lines, i + 1, last);
      for (let k = 0; k < body.length; k++) {
        if (!blank(body[k]!)) throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(v4aDelete(path));
      i = end;
      continue;
    }
    if ((m = /^\*\*\* Update File: (.*)$/.exec(line)) !== null) {
      const path = m[1]!.trim();
      const { body, end } = collectV4aSection(lines, i + 1, last);
      edits.push(v4aUpdate(path, body, i, strict));
      i = end;
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return edits;
}

/* ------------------------------------------------------------------ section 9: JSON */

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ section 10: run */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(parseUnified(lines), strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const changed = [...tree.now.keys()].filter((p) => tree.original(p) !== tree.now.get(p));
  const rows: { key: string; line: string }[] = [];
  const usedOld = new Set<string>();
  const usedNew = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (usedOld.has(oldP) || usedNew.has(newP)) continue;
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, line: `R ${oldP} -> ${newP}` });
      usedOld.add(oldP);
      usedNew.add(newP);
    }
  }
  for (const p of changed) {
    if (usedOld.has(p) || usedNew.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of changed) {
      const now = tree.now.get(p)!;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
