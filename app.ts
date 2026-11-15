// A GitHub-compatible git forge: REST v3, git smart HTTP (v2 + v0), GraphQL v4, MCP.
// Original implementation for the make.fun github-core-clone-01 competition.
// Node 22 stdlib only, one process, fully in-memory, deterministic state:
// server-created timestamps come from a monotonic sequence counter, never the wall clock.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const ZERO_OID = '0000000000000000000000000000000000000000';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const FIXED_NOW = process.env.MAKEFUN_TRIAL_NOW ?? '2026-11-14T06:30:00Z';
const COMMIT_EPOCH = 1700000000;

// ------------------------------------------------------------------ state

let seq = 0;
function nextSeq(): number { seq += 1; return seq; }

let viewerLogin: string | null = null;
function learnViewer(login: string): void {
  if (!viewerLogin && login) viewerLogin = login;
}
function viewer(): string { return viewerLogin ?? 'octocat'; }

interface Label { name: string; color: string; description: string }
interface Comment { id: number; nodeId: string; body: string; user: string; seq: number }
interface Issue {
  id: number; nodeId: string; number: number; title: string; body: string;
  state: 'open' | 'closed'; labels: Label[]; comments: Comment[]; seq: number;
}
interface Pull {
  id: number; nodeId: string; number: number; title: string; body: string;
  state: 'open' | 'closed'; merged: boolean; mergedAt: string | null; mergeSha: string | null;
  head: string; base: string; seq: number;
}
interface GitObject { type: string; data: Buffer; oid: string }
interface Repo {
  id: number; nodeId: string; name: string; owner: string; description: string; isPrivate: boolean;
  defaultBranch: string; seq: number;
  refs: Map<string, string>;
  objects: Map<string, GitObject>;
  issues: Issue[]; pulls: Pull[]; labels: Label[];
  nextNumber: number;
}

const repos = new Map<string, Repo>();
let nextRepoId = 1;
let nextGlobalId = 100000;

function gid(kind: string, key: string): string {
  return Buffer.from(`${kind}:${key}`, 'utf8').toString('base64');
}

// ------------------------------------------------------------------ git objects

function sha1(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}
function hashObject(type: string, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1(Buffer.concat([header, data]));
}
function storeObject(repo: Repo, type: string, data: Buffer): GitObject {
  const oid = hashObject(type, data);
  let obj = repo.objects.get(oid);
  if (!obj) { obj = { type, data, oid }; repo.objects.set(oid, obj); }
  return obj;
}
function getObject(repo: Repo, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}

interface CommitParts { tree: string; parents: string[]; author: string; committer: string; message: string }
function parseCommit(data: Buffer): CommitParts {
  const text = data.toString('utf8');
  const headEnd = text.indexOf('\n\n');
  const head = headEnd >= 0 ? text.slice(0, headEnd) : text;
  const message = headEnd >= 0 ? text.slice(headEnd + 2) : '';
  const parts: CommitParts = { tree: '', parents: [], author: '', committer: '', message };
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) parts.tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parts.parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) parts.author = line.slice(7);
    else if (line.startsWith('committer ')) parts.committer = line.slice(10);
  }
  return parts;
}
function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string, authorName: string, authorEmail: string): GitObject {
  const epoch = COMMIT_EPOCH + nextSeq();
  const who = `${authorName} <${authorEmail}> ${epoch} +0000`;
  let text = `tree ${treeOid}\n`;
  for (const p of parents) text += `parent ${p}\n`;
  text += `author ${who}\ncommitter ${who}\n\n${message}\n`;
  return storeObject(repo, 'commit', Buffer.from(text, 'utf8'));
}
interface TreeEntry { mode: string; name: string; oid: string }
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let i = 0;
  while (i < data.length) {
    const sp = data.indexOf(0x20, i);
    if (sp < 0) break;
    const mode = data.subarray(i, sp).toString('utf8');
    const nul = data.indexOf(0, sp);
    if (nul < 0) break;
    const name = data.subarray(sp + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    i = nul + 21;
  }
  return entries;
}
function treeSortKey(e: TreeEntry): string {
  return e.mode === '40000' ? `${e.name}/` : e.name;
}
function makeTree(repo: Repo, entries: TreeEntry[]): GitObject {
  const sorted = [...entries].sort((a, b) => (treeSortKey(a) < treeSortKey(b) ? -1 : treeSortKey(a) > treeSortKey(b) ? 1 : 0));
  const chunks: Buffer[] = [];
  for (const e of sorted) {
    chunks.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    chunks.push(Buffer.from(e.oid, 'hex'));
  }
  return storeObject(repo, 'tree', Buffer.concat(chunks));
}
// Flat path map (path -> {oid, mode}) for a tree.
function flatTree(repo: Repo, treeOid: string, prefix = '', out: Map<string, { oid: string; mode: string }> = new Map()): Map<string, { oid: string; mode: string }> {
  const obj = getObject(repo, treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flatTree(repo, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
  return out;
}
function buildTree(repo: Repo, files: Map<string, { oid: string; mode: string }>): GitObject {
  const build = (map: Map<string, { oid: string; mode: string }>, paths: string[]): GitObject => {
    const entries: TreeEntry[] = [];
    const dirs = new Map<string, string[]>();
    for (const p of paths) {
      const slash = p.indexOf('/');
      if (slash < 0) {
        const f = map.get(p)!;
        entries.push({ mode: f.mode, name: p, oid: f.oid });
      } else {
        const dir = p.slice(0, slash);
        if (!dirs.has(dir)) dirs.set(dir, []);
        dirs.get(dir)!.push(p.slice(slash + 1));
      }
    }
    for (const [dir, sub] of dirs) {
      const deeper = new Map<string, { oid: string; mode: string }>();
      for (const sp of sub) deeper.set(sp, map.get(`${dir}/${sp}`)!);
      entries.push({ mode: '40000', name: dir, oid: build(deeper, sub).oid });
    }
    return makeTree(repo, entries);
  };
  return build(files, [...files.keys()]);
}
function commitTree(repo: Repo, commitOid: string): string {
  const obj = getObject(repo, commitOid);
  if (!obj || obj.type !== 'commit') return '';
  return parseCommit(obj.data).tree;
}
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const stack = [descendant];
  while (stack.length) {
    const cur = stack.pop()!;
    if (cur === ancestor) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.type === 'commit') stack.push(...parseCommit(obj.data).parents);
  }
  return false;
}
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancA = new Set<string>();
  const stack = [a];
  while (stack.length) {
    const cur = stack.pop()!;
    if (ancA.has(cur)) continue;
    ancA.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.type === 'commit') stack.push(...parseCommit(obj.data).parents);
  }
  const stackB = [b];
  const seenB = new Set<string>();
  while (stackB.length) {
    const cur = stackB.pop()!;
    if (ancA.has(cur)) return cur;
    if (seenB.has(cur)) continue;
    seenB.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.type === 'commit') stackB.push(...parseCommit(obj.data).parents);
  }
  return null;
}
// All objects reachable from tips (commits -> parents/trees/blobs; tags -> target).
function reachableObjects(repo: Repo, tips: string[]): Map<string, GitObject> {
  const out = new Map<string, GitObject>();
  const stack = [...tips];
  const seen = new Set<string>();
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (!obj) continue;
    out.set(oid, obj);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree, ...c.parents);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      const m = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m);
      if (m) stack.push(m[1]);
    }
  }
  return out;
}
function peelToCommit(repo: Repo, oid: string): string {
  let cur = oid;
  for (let i = 0; i < 8; i += 1) {
    const obj = getObject(repo, cur);
    if (!obj) return cur;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') {
      const m = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m);
      if (!m) return cur;
      cur = m[1];
    } else return cur;
  }
  return cur;
}

// ------------------------------------------------------------------ pkt-line

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = data.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
type Pkt = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' };
function parsePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let i = 0;
  while (i + 4 <= buf.length) {
    const lenHex = buf.subarray(i, i + 4).toString('ascii');
    if (lenHex === '0000') { out.push({ kind: 'flush' }); i += 4; continue; }
    if (lenHex === '0001') { out.push({ kind: 'delim' }); i += 4; continue; }
    const len = parseInt(lenHex, 16);
    if (Number.isNaN(len) || len < 4 || i + len > buf.length) throw new Error(`bad pkt-line length ${lenHex}`);
    out.push({ kind: 'data', payload: buf.subarray(i + 4, i + len) });
    i += len;
  }
  return out;
}

// ------------------------------------------------------------------ pack files

const PACK_TYPES: Record<number, string> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag', 6: 'ofs-delta', 7: 'ref-delta' };
function encodePack(objects: GitObject[]): Buffer {
  const parts: Buffer[] = [Buffer.from('PACK', 'ascii')];
  const header = Buffer.alloc(8);
  header.writeUInt32BE(2, 0);
  header.writeUInt32BE(objects.length, 4);
  parts.push(header);
  for (const obj of objects) {
    const typeNum = ({ commit: 1, tree: 2, blob: 3, tag: 4 })[obj.type] ?? 3;
    const size = obj.data.length;
    const sizeBytes: number[] = [];
    let remaining = size;
    let first = (typeNum << 4) | (remaining & 0x0f);
    remaining >>= 4;
    if (remaining > 0) first |= 0x80;
    sizeBytes.push(first);
    while (remaining > 0) {
      let b = remaining & 0x7f;
      remaining >>= 7;
      if (remaining > 0) b |= 0x80;
      sizeBytes.push(b);
    }
    parts.push(Buffer.from(sizeBytes), deflateSync(obj.data, { level: 6 }));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let i = 0;
  const readVarint = (): number => {
    let result = 0;
    let shift = 0;
    while (i < delta.length) {
      const b = delta[i]; i += 1;
      result |= (b & 0x7f) << shift;
      shift += 7;
      if ((b & 0x80) === 0) break;
    }
    return result;
  };
  const srcSize = readVarint();
  const dstSize = readVarint();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out: Buffer[] = [];
  while (i < delta.length) {
    const op = delta[i]; i += 1;
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      if (op & 0x01) { offset = delta[i]; i += 1; }
      if (op & 0x02) { offset |= delta[i] << 8; i += 1; }
      if (op & 0x04) { offset |= delta[i] << 16; i += 1; }
      if (op & 0x08) { offset |= delta[i] << 24; i += 1; }
      if (op & 0x10) { size = delta[i]; i += 1; }
      if (op & 0x20) { size |= delta[i] << 8; i += 1; }
      if (op & 0x40) { size |= delta[i] << 16; i += 1; }
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
    } else if (op > 0) {
      out.push(delta.subarray(i, i + op));
      i += op;
    } else throw new Error('delta opcode 0');
  }
  const result = Buffer.concat(out);
  if (result.length !== dstSize) throw new Error('delta result size mismatch');
  return result;
}
// Decode a pack. `resolveBase` finds objects already in the repo (thin packs).
function decodePack(buf: Buffer, resolveBase?: (oid: string) => GitObject | undefined): GitObject[] {
  if (buf.length < 32 || buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a pack');
  const count = buf.readUInt32BE(8);
  const objects: GitObject[] = [];
  const byOffset = new Map<number, GitObject>();
  const byOid = new Map<string, GitObject>();
  let pos = 12;
  // inflateSync ignores trailing bytes and throws when truncated, so the smallest
  // slice that inflates is the end of this object's zlib stream.
  const inflateAt = (start: number): { data: Buffer; end: number } => {
    let lo = start;
    let hi = buf.length;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      try { inflateSync(buf.subarray(start, mid)); hi = mid; } catch { lo = mid + 1; }
    }
    return { data: inflateSync(buf.subarray(start, lo)), end: lo };
  };
  for (let n = 0; n < count; n += 1) {
    const start = pos;
    let b = buf[pos]; pos += 1;
    const typeNum = (b >> 4) & 0x07;
    let size = b & 0x0f;
    let shift = 4;
    while (b & 0x80) {
      b = buf[pos]; pos += 1;
      size |= (b & 0x7f) << shift;
      shift += 7;
    }
    let baseOid: string | null = null;
    let baseOffset = 0;
    if (typeNum === 6) {
      b = buf[pos]; pos += 1;
      let offset = b & 0x7f;
      while (b & 0x80) {
        b = buf[pos]; pos += 1;
        offset = ((offset + 1) << 7) | (b & 0x7f);
      }
      baseOffset = start - offset;
    } else if (typeNum === 7) {
      baseOid = buf.subarray(pos, pos + 20).toString('hex');
      pos += 20;
    }
    const { data: inflated, end } = inflateAt(pos);
    pos = end;
    if (typeNum === 6 || typeNum === 7) {
      const base = typeNum === 6
        ? byOffset.get(baseOffset)
        : (byOid.get(baseOid!) ?? resolveBase?.(baseOid!));
      if (!base) throw new Error('delta base missing');
      const data = applyDelta(base.data, inflated);
      const obj: GitObject = { type: base.type, data, oid: hashObject(base.type, data) };
      objects.push(obj);
      byOffset.set(start, obj);
      byOid.set(obj.oid, obj);
      continue;
    }
    const type = PACK_TYPES[typeNum];
    if (!type) throw new Error(`unknown pack type ${typeNum}`);
    if (inflated.length !== size) throw new Error('pack object size mismatch');
    const obj: GitObject = { type, data: inflated, oid: hashObject(type, inflated) };
    objects.push(obj);
    byOffset.set(start, obj);
    byOid.set(obj.oid, obj);
  }
  return objects;
}

// ------------------------------------------------------------------ repo store

function createRepo(name: string, description: string, isPrivate: boolean): Repo {
  const id = nextRepoId;
  nextRepoId += 1;
  const repo: Repo = {
    id, nodeId: gid('Repository', String(id)), name, owner: viewer(), description, isPrivate,
    defaultBranch: 'main', seq: nextSeq(),
    refs: new Map(), objects: new Map(), issues: [], pulls: [], labels: [],
    nextNumber: 1,
  };
  repos.set(name, repo);
  return repo;
}
function findRepo(owner: string, name: string): Repo | null {
  if (owner !== viewer()) return null;
  return repos.get(name) ?? null;
}
function refTip(repo: Repo, branch: string): string | null {
  return repo.refs.get(`refs/heads/${branch}`) ?? null;
}
function listBranches(repo: Repo): { name: string; sha: string }[] {
  const out: { name: string; sha: string }[] = [];
  for (const [ref, oid] of repo.refs) {
    if (ref.startsWith('refs/heads/')) out.push({ name: ref.slice('refs/heads/'.length), sha: oid });
  }
  out.sort((a, b) => (a.name < b.name ? -1 : 1));
  return out;
}
function listCommits(repo: Repo, tip: string): { sha: string; message: string; parents: string[]; tree: string }[] {
  const out: { sha: string; message: string; parents: string[]; tree: string }[] = [];
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    const c = parseCommit(obj.data);
    out.push({ sha: oid, message: c.message.replace(/\n$/, ''), parents: c.parents, tree: c.tree });
    stack.push(...c.parents);
  }
  return out;
}
// Commit a new version of one file on a branch (creating the branch from the
// default tip when needed). Returns the new commit object and whether the file existed.
function commitFile(repo: Repo, branch: string, path: string, content: Buffer, message: string): { commit: GitObject; created: boolean; blobOid: string } {
  let tip = refTip(repo, branch);
  if (!tip) {
    const defaultTip = refTip(repo, repo.defaultBranch);
    if (defaultTip && branch !== repo.defaultBranch) {
      repo.refs.set(`refs/heads/${branch}`, defaultTip);
      tip = defaultTip;
    }
  }
  const baseFiles = tip ? flatTree(repo, commitTree(repo, tip)) : new Map<string, { oid: string; mode: string }>();
  const created = !baseFiles.has(path);
  const blob = storeObject(repo, 'blob', content);
  baseFiles.set(path, { oid: blob.oid, mode: '100644' });
  const tree = buildTree(repo, baseFiles);
  const parents = tip ? [tip] : [];
  const commit = makeCommit(repo, tree.oid, parents, message, viewer(), `${viewer()}@example.invalid`);
  repo.refs.set(`refs/heads/${branch}`, commit.oid);
  return { commit, created, blobOid: blob.oid };
}
function deleteFile(repo: Repo, branch: string, path: string, message: string): GitObject | null {
  const tip = refTip(repo, branch);
  if (!tip) return null;
  const baseFiles = flatTree(repo, commitTree(repo, tip));
  if (!baseFiles.has(path)) return null;
  baseFiles.delete(path);
  const tree = buildTree(repo, baseFiles);
  const commit = makeCommit(repo, tree.oid, [tip], message, viewer(), `${viewer()}@example.invalid`);
  repo.refs.set(`refs/heads/${branch}`, commit.oid);
  return commit;
}
// Diff two flat trees: path -> status.
interface FileChange { path: string; status: 'added' | 'removed' | 'modified'; oldOid: string | null; newOid: string | null }
function diffFiles(a: Map<string, { oid: string; mode: string }>, b: Map<string, { oid: string; mode: string }>): FileChange[] {
  const out: FileChange[] = [];
  const keys = new Set([...a.keys(), ...b.keys()]);
  for (const k of keys) {
    const av = a.get(k);
    const bv = b.get(k);
    if (!av && bv) out.push({ path: k, status: 'added', oldOid: null, newOid: bv.oid });
    else if (av && !bv) out.push({ path: k, status: 'removed', oldOid: av.oid, newOid: null });
    else if (av && bv && av.oid !== bv.oid) out.push({ path: k, status: 'modified', oldOid: av.oid, newOid: bv.oid });
  }
  out.sort((x, y) => (x.path < y.path ? -1 : 1));
  return out;
}
function prFiles(repo: Repo, pr: Pull): FileChange[] {
  const baseTip = refTip(repo, pr.base);
  const headTip = refTip(repo, pr.head);
  if (!baseTip || !headTip) return [];
  return diffFiles(flatTree(repo, commitTree(repo, baseTip)), flatTree(repo, commitTree(repo, headTip)));
}
function prConflicted(repo: Repo, pr: Pull): boolean {
  const baseTip = refTip(repo, pr.base);
  const headTip = refTip(repo, pr.head);
  if (!baseTip || !headTip) return false;
  const base = mergeBase(repo, baseTip, headTip);
  if (!base) return false;
  const baseFiles = flatTree(repo, commitTree(repo, base));
  const baseNow = flatTree(repo, commitTree(repo, baseTip));
  const headNow = flatTree(repo, commitTree(repo, headTip));
  const baseChanges = diffFiles(baseFiles, baseNow);
  const headChanges = diffFiles(baseFiles, headNow);
  const headByPath = new Map(headChanges.map((c) => [c.path, c]));
  for (const bc of baseChanges) {
    const hc = headByPath.get(bc.path);
    if (hc && hc.newOid !== bc.newOid) return true;
  }
  return false;
}
function squashMerge(repo: Repo, pr: Pull): GitObject | null {
  const baseTip = refTip(repo, pr.base);
  const headTip = refTip(repo, pr.head);
  if (!baseTip || !headTip) return null;
  const headFiles = flatTree(repo, commitTree(repo, headTip));
  const tree = buildTree(repo, headFiles);
  const commit = makeCommit(repo, tree.oid, [baseTip], `Merge pull request #${pr.number} (${pr.title})`, viewer(), `${viewer()}@example.invalid`);
  repo.refs.set(`refs/heads/${pr.base}`, commit.oid);
  return commit;
}

// ------------------------------------------------------------------ serializers

function userJson(login: string): Record<string, unknown> {
  return { login, id: 1000, node_id: gid('User', login), type: 'User', site_admin: false, email: `${login}@example.invalid`, name: login };
}
function repoJson(repo: Repo): Record<string, unknown> {
  const o = repo.owner;
  return {
    id: repo.id, node_id: repo.nodeId, name: repo.name, full_name: `${o}/${repo.name}`,
    owner: userJson(o), private: repo.isPrivate, description: repo.description,
    default_branch: repo.defaultBranch, html_url: `https://example.invalid/${o}/${repo.name}`,
    clone_url: `https://example.invalid/${o}/${repo.name}.git`, git_url: `git://example.invalid/${o}/${repo.name}.git`,
    ssh_url: `git@example.invalid:${o}/${repo.name}.git`,
    url: `/api/v3/repos/${o}/${repo.name}`,
    created_at: FIXED_NOW, updated_at: FIXED_NOW, pushed_at: FIXED_NOW,
    has_issues: true, has_projects: true, has_wiki: true, has_pages: false,
    forks_count: 0, open_issues_count: repo.issues.filter((i) => i.state === 'open').length,
    watchers_count: 0, stargazers_count: 0, subscribers_count: 0, size: 0,
    license: null, topics: [], visibility: repo.isPrivate ? 'private' : 'public',
    archived: false, disabled: false, fork: false, mirror_url: null, language: null,
  };
}
function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id, node_id: issue.nodeId, number: issue.number, title: issue.title, body: issue.body,
    state: issue.state, locked: false, user: userJson(repo.owner),
    labels: issue.labels.map((l) => ({ name: l.name, color: l.color, description: l.description, url: '', default: false })),
    assignees: [], assignee: null, milestone: null, comments: issue.comments.length,
    created_at: FIXED_NOW, updated_at: FIXED_NOW, closed_at: issue.state === 'closed' ? FIXED_NOW : null,
    author_association: 'OWNER', active_lock_reason: null,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    comments_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/comments`,
    events_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/events`,
    labels_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}/labels{/name}`,
  };
}
function pullJson(repo: Repo, pr: Pull): Record<string, unknown> {
  const headTip = refTip(repo, pr.head);
  const baseTip = refTip(repo, pr.base);
  return {
    id: pr.id, node_id: pr.nodeId, number: pr.number, title: pr.title, body: pr.body,
    state: pr.state, locked: false, draft: false, merged: pr.merged,
    mergeable: !prConflicted(repo, pr), mergeable_state: prConflicted(repo, pr) ? 'dirty' : 'clean',
    merged_at: pr.mergedAt, merge_commit_sha: pr.mergeSha,
    user: userJson(repo.owner),
    head: { ref: pr.head, sha: headTip, label: `${repo.owner}:${pr.head}`, user: userJson(repo.owner), repo: repoJson(repo) },
    base: { ref: pr.base, sha: baseTip, label: `${repo.owner}:${pr.base}`, user: userJson(repo.owner), repo: repoJson(repo) },
    created_at: FIXED_NOW, updated_at: FIXED_NOW, closed_at: pr.state === 'closed' ? FIXED_NOW : null,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`,
    commits: listCommits(repo, headTip ?? '').length,
    additions: 0, deletions: 0, changed_files: prFiles(repo, pr).length,
  };
}
function countLines(buf: Buffer): number {
  const text = buf.toString('utf8');
  if (text === '') return 0;
  return text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
}
function lineCounts(repo: Repo, change: FileChange): { additions: number; deletions: number } {
  const oldText = change.oldOid ? (getObject(repo, change.oldOid)?.data ?? Buffer.alloc(0)) : Buffer.alloc(0);
  const newText = change.newOid ? (getObject(repo, change.newOid)?.data ?? Buffer.alloc(0)) : Buffer.alloc(0);
  if (change.status === 'added') return { additions: Math.max(1, countLines(newText)), deletions: 0 };
  if (change.status === 'removed') return { additions: 0, deletions: Math.max(1, countLines(oldText)) };
  const oldLines = new Set(oldText.toString('utf8').split('\n'));
  const newLines = newText.toString('utf8').split('\n');
  let additions = 0;
  for (const l of newLines) if (!oldLines.has(l)) additions += 1;
  const newSet = new Set(newLines);
  let deletions = 0;
  for (const l of oldText.toString('utf8').split('\n')) if (!newSet.has(l)) deletions += 1;
  return { additions: Math.max(1, additions), deletions };
}

// ------------------------------------------------------------------ HTTP helpers

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), 'x-github-request-id': `req-${nextSeq()}`, ...headers });
  res.end(text);
}
function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string, headers: Readonly<Record<string, string>> = {}): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length, 'x-github-request-id': `req-${nextSeq()}`, ...headers });
  res.end(body);
}
function errJson(res: ServerResponse, status: number, message: string, extra: Readonly<Record<string, string>> = {}): void {
  sendJson(res, status, { message }, extra);
}
function pathOf(req: IncomingMessage): string {
  try { return new URL(req.url ?? '/', 'http://entry').pathname; } catch { return '/'; }
}
function queryOf(req: IncomingMessage): URLSearchParams {
  try { return new URL(req.url ?? '/', 'http://entry').searchParams; } catch { return new URLSearchParams(); }
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (c: Buffer) => { chunks.push(c); if (Buffer.concat(chunks).length > 64 * 1024 * 1024) reject(new Error('body too large')); });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function parseJsonBody(buf: Buffer): { ok: boolean; value: unknown } {
  if (buf.length === 0) return { ok: true, value: undefined };
  try { return { ok: true, value: JSON.parse(buf.toString('utf8')) }; } catch { return { ok: false, value: undefined }; }
}
function authOk(req: IncomingMessage): boolean {
  if (!TOKEN) return true;
  const h = req.headers.authorization ?? '';
  return h === `Bearer ${TOKEN}`;
}
function pageParams(q: URLSearchParams): { page: number; perPage: number } {
  const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
  const perPage = Math.min(100, Math.max(1, parseInt(q.get('per_page') ?? '30', 10) || 30));
  return { page, perPage };
}
function paginate<T>(items: T[], q: URLSearchParams, req: IncomingMessage, path: string): { page: T[]; link: string | null } {
  const { page, perPage } = pageParams(q);
  const start = (page - 1) * perPage;
  const pageItems = items.slice(start, start + perPage);
  let link: string | null = null;
  if (start + perPage < items.length) {
    const host = req.headers.host ?? 'entry';
    const nextQ = new URLSearchParams(q);
    nextQ.set('page', String(page + 1));
    nextQ.set('per_page', String(perPage));
    link = `<http://${host}${path}?${nextQ.toString()}>; rel="next"`;
  }
  return { page: pageItems, link };
}

// ------------------------------------------------------------------ REST v3

function decodePath(p: string): string {
  try { return decodeURIComponent(p); } catch { return p; }
}
function resolveRef(repo: Repo, ref: string | null): string | null {
  if (!ref) return refTip(repo, repo.defaultBranch);
  if (repo.refs.has(`refs/heads/${ref}`)) return repo.refs.get(`refs/heads/${ref}`)!;
  if (repo.refs.has(ref)) return repo.refs.get(ref)!;
  if (getObject(repo, ref)?.type === 'commit') return ref;
  return null;
}

async function handleRest(req: IncomingMessage, res: ServerResponse, path: string, bodyBuf: Buffer): Promise<boolean> {
  if (!path.startsWith('/api/v3')) return false;
  const method = req.method ?? 'GET';
  const q = queryOf(req);
  if (!authOk(req)) { errJson(res, 401, 'Requires authentication'); return true; }
  const sub = path.slice('/api/v3'.length);
  const body = parseJsonBody(bodyBuf);
  if (!body.ok) { errJson(res, 400, 'Problems parsing JSON'); return true; }
  const b = (body.value ?? {}) as Record<string, unknown>;

  if (method === 'GET' && (sub === '' || sub === '/')) {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (method === 'GET' && sub === '/meta') {
    sendJson(res, 200, { verifiable_password_authentication: true, installed_version: '1.0.0', api: ['v3'], git: ['v2'] });
    return true;
  }
  if (method === 'GET' && sub === '/rate_limit') {
    sendJson(res, 200, { resources: { core: { limit: 5000, remaining: 4999, reset: COMMIT_EPOCH } }, rate: { limit: 5000, remaining: 4999, reset: COMMIT_EPOCH } });
    return true;
  }
  if (method === 'GET' && sub === '/user') {
    sendJson(res, 200, userJson(viewer()));
    return true;
  }
  if (sub === '/user/repos') {
    if (method === 'GET') {
      const all = [...repos.values()].sort((a, c) => a.seq - c.seq).map(repoJson);
      const { page, link } = paginate(all, q, req, '/api/v3/user/repos');
      sendJson(res, 200, page, link ? { link } : {});
      return true;
    }
    if (method === 'POST') {
      const name = typeof b.name === 'string' ? b.name : '';
      if (!name) { errJson(res, 422, 'Validation Failed: name is required'); return true; }
      if (repos.has(name)) { errJson(res, 422, 'Repository already exists'); return true; }
      const repo = createRepo(name, typeof b.description === 'string' ? b.description : '', b.private === true);
      sendJson(res, 201, repoJson(repo));
      return true;
    }
  }

  const repoMatch = sub.match(/^\/repos\/([^/]+)\/([^/]+)(\/.*)?$/);
  if (!repoMatch) { errJson(res, 404, 'Not Found'); return true; }
  const owner = decodePath(repoMatch[1]);
  const repoName = decodePath(repoMatch[2]);
  const rest = repoMatch[3] ?? '';
  const repo = findRepo(owner, repoName);
  if (!repo) { errJson(res, 404, 'Not Found'); return true; }

  if (rest === '' || rest === '/') {
    if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return true; }
    if (method === 'PATCH') {
      if (typeof b.description === 'string') repo.description = b.description;
      if (b.private === true || b.private === false) repo.isPrivate = b.private;
      sendJson(res, 200, repoJson(repo));
      return true;
    }
    if (method === 'DELETE') {
      repos.delete(repo.name);
      res.writeHead(204, { 'x-github-request-id': `req-${nextSeq()}` });
      res.end();
      return true;
    }
  }

  if (rest === '/branches' && method === 'GET') {
    sendJson(res, 200, listBranches(repo).map((br) => ({ name: br.name, commit: { sha: br.sha, url: `/api/v3/repos/${owner}/${repoName}/commits/${br.sha}` }, protected: false })));
    return true;
  }
  const branchMatch = rest.match(/^\/branches\/([^/]+)$/);
  if (branchMatch && method === 'GET') {
    const br = decodePath(branchMatch[1]);
    const tip = refTip(repo, br);
    if (!tip) { errJson(res, 404, 'Not Found'); return true; }
    sendJson(res, 200, { name: br, commit: { sha: tip, url: `/api/v3/repos/${owner}/${repoName}/commits/${tip}` }, protected: false });
    return true;
  }
  if (rest === '/commits' && method === 'GET') {
    const tip = resolveRef(repo, q.get('sha'));
    if (!tip) { errJson(res, 404, 'Not Found'); return true; }
    const list = listCommits(repo, tip).map((c) => ({
      sha: c.sha, commit: { message: c.message, author: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW }, committer: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW }, tree: { sha: c.tree } },
      author: userJson(viewer()), committer: userJson(viewer()), parents: c.parents.map((p) => ({ sha: p })),
      url: `/api/v3/repos/${owner}/${repoName}/commits/${c.sha}`,
    }));
    const { page, link } = paginate(list, q, req, `/api/v3/repos/${owner}/${repoName}/commits`);
    sendJson(res, 200, page, link ? { link } : {});
    return true;
  }
  const commitMatch = rest.match(/^\/commits\/([0-9a-f]{40})$/);
  if (commitMatch && method === 'GET') {
    const obj = getObject(repo, commitMatch[1]);
    if (!obj || obj.type !== 'commit') { errJson(res, 404, 'Not Found'); return true; }
    const c = parseCommit(obj.data);
    sendJson(res, 200, {
      sha: commitMatch[1], commit: { message: c.message.replace(/\n$/, ''), author: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW }, committer: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW }, tree: { sha: c.tree } },
      author: userJson(viewer()), committer: userJson(viewer()), parents: c.parents.map((p) => ({ sha: p })),
    });
    return true;
  }

  // Git Data API: refs
  if (rest === '/git/refs' && method === 'GET') {
    const all = [...repo.refs.entries()].map(([ref, oid]) => ({ ref, object: { sha: oid, type: getObject(repo, oid)?.type ?? 'commit', url: '' } }));
    sendJson(res, 200, all);
    return true;
  }
  const refMatch = rest.match(/^\/git\/refs\/(.+)$/);
  if (refMatch && method === 'GET') {
    const ref = `refs/${decodePath(refMatch[1])}`;
    const oid = repo.refs.get(ref);
    if (!oid) { errJson(res, 404, 'Not Found'); return true; }
    sendJson(res, 200, { ref, object: { sha: oid, type: getObject(repo, oid)?.type ?? 'commit', url: '' } });
    return true;
  }
  if (rest === '/git/refs' && method === 'POST') {
    const ref = typeof b.ref === 'string' ? b.ref : '';
    const sha = typeof b.sha === 'string' ? b.sha : '';
    if (!ref || !sha || !getObject(repo, sha)) { errJson(res, 422, 'Validation Failed'); return true; }
    if (repo.refs.has(ref)) { errJson(res, 422, 'Reference already exists'); return true; }
    repo.refs.set(ref, sha);
    sendJson(res, 201, { ref, object: { sha, type: getObject(repo, sha)?.type ?? 'commit', url: '' } });
    return true;
  }

  // Contents
  const contentsMatch = rest.match(/^\/contents(?:\/(.*))?$/);
  if (contentsMatch) {
    const rawPath = contentsMatch[1] ?? '';
    const filePath = decodePath(rawPath);
    if (method === 'PUT') {
      const message = typeof b.message === 'string' ? b.message : `Update ${filePath}`;
      const contentB64 = typeof b.content === 'string' ? b.content : '';
      const branch = typeof b.branch === 'string' ? b.branch : repo.defaultBranch;
      const content = Buffer.from(contentB64.replace(/\s+/g, ''), 'base64');
      const tip = resolveRef(repo, branch);
      if (b.sha !== undefined && typeof b.sha === 'string' && tip) {
        const current = flatTree(repo, commitTree(repo, tip)).get(filePath);
        if (current && current.oid !== b.sha) { errJson(res, 409, 'Conflict: sha does not match'); return true; }
      }
      const { commit, created, blobOid } = commitFile(repo, branch, filePath, content, message);
      const name = filePath.split('/').pop() ?? filePath;
      sendJson(res, created ? 201 : 200, {
        content: { name, path: filePath, sha: blobOid, size: content.length, type: 'file', encoding: 'base64', content: content.toString('base64'), url: `/api/v3/repos/${owner}/${repoName}/contents/${filePath}` },
        commit: { sha: commit.oid, message, author: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW }, committer: { name: viewer(), email: `${viewer()}@example.invalid`, date: FIXED_NOW } },
      });
      return true;
    }
    if (method === 'GET') {
      const tip = resolveRef(repo, q.get('ref'));
      if (!tip) { errJson(res, 404, 'Not Found'); return true; }
      const files = flatTree(repo, commitTree(repo, tip));
      if (filePath === '') {
        sendJson(res, 200, dirListing(repo, files, ''));
        return true;
      }
      const file = files.get(filePath);
      if (file) {
        const data = getObject(repo, file.oid)?.data ?? Buffer.alloc(0);
        sendJson(res, 200, {
          type: 'file', encoding: 'base64', content: data.toString('base64'), sha: file.oid, size: data.length,
          name: filePath.split('/').pop(), path: filePath,
          url: `/api/v3/repos/${owner}/${repoName}/contents/${filePath}`,
        });
        return true;
      }
      const prefix = `${filePath}/`;
      if ([...files.keys()].some((k) => k.startsWith(prefix))) {
        sendJson(res, 200, dirListing(repo, files, filePath));
        return true;
      }
      errJson(res, 404, 'Not Found');
      return true;
    }
    if (method === 'DELETE') {
      const message = typeof b.message === 'string' ? b.message : `Delete ${filePath}`;
      const branch = typeof b.branch === 'string' ? b.branch : repo.defaultBranch;
      const commit = deleteFile(repo, branch, filePath, message);
      if (!commit) { errJson(res, 404, 'Not Found'); return true; }
      sendJson(res, 200, { commit: { sha: commit.oid, message }, content: null });
      return true;
    }
  }

  // Labels
  if (rest === '/labels' && method === 'GET') {
    sendJson(res, 200, repo.labels.map((l) => ({ name: l.name, color: l.color, description: l.description, url: '', default: false })));
    return true;
  }
  if (rest === '/labels' && method === 'POST') {
    const name = typeof b.name === 'string' ? b.name : '';
    if (!name) { errJson(res, 422, 'Validation Failed: name is required'); return true; }
    const color = typeof b.color === 'string' ? b.color.replace(/^#/, '') : 'ededed';
    const description = typeof b.description === 'string' ? b.description : '';
    const existing = repo.labels.find((l) => l.name === name);
    if (existing) { existing.color = color; existing.description = description; }
    else repo.labels.push({ name, color, description });
    sendJson(res, 201, { name, color, description, url: '', default: false });
    return true;
  }

  // Issues
  if (rest === '/issues' && method === 'GET') {
    const state = q.get('state') ?? 'open';
    let list = repo.issues.slice();
    if (state !== 'all') list = list.filter((i) => i.state === state);
    const direction = q.get('direction') ?? 'desc';
    list.sort((a, c) => (direction === 'asc' ? a.seq - c.seq : c.seq - a.seq));
    const { page, link } = paginate(list.map((i) => issueJson(repo, i)), q, req, `/api/v3/repos/${owner}/${repoName}/issues`);
    sendJson(res, 200, page, link ? { link } : {});
    return true;
  }
  if (rest === '/issues' && method === 'POST') {
    const title = typeof b.title === 'string' ? b.title : '';
    const labelsIn = Array.isArray(b.labels) ? b.labels : [];
    const labels: Label[] = [];
    for (const l of labelsIn) {
      const name = typeof l === 'string' ? l : (l as Record<string, unknown>)?.name;
      if (typeof name !== 'string') continue;
      const found = repo.labels.find((x) => x.name === name);
      if (!found) { errJson(res, 422, `Validation Failed: label "${name}" does not exist`); return true; }
      labels.push(found);
    }
    const number = repo.nextNumber;
    repo.nextNumber += 1;
    const id = nextGlobalId;
    nextGlobalId += 1;
    const issue: Issue = { id, nodeId: gid('Issue', `${repo.id}:${number}`), number, title, body: typeof b.body === 'string' ? b.body : '', state: 'open', labels, comments: [], seq: nextSeq() };
    repo.issues.push(issue);
    sendJson(res, 201, issueJson(repo, issue));
    return true;
  }
  const issueMatch = rest.match(/^\/issues\/(\d+)(\/comments)?$/);
  if (issueMatch) {
    const number = parseInt(issueMatch[1], 10);
    const issue = repo.issues.find((i) => i.number === number);
    if (!issue) { errJson(res, 404, 'Not Found'); return true; }
    if (issueMatch[2] === '/comments') {
      if (method === 'GET') {
        sendJson(res, 200, issue.comments.map((c) => ({ id: c.id, node_id: c.nodeId, body: c.body, user: userJson(repo.owner), created_at: FIXED_NOW, updated_at: FIXED_NOW, url: '', html_url: '' })));
        return true;
      }
      if (method === 'POST') {
        const id = nextGlobalId;
        nextGlobalId += 1;
        const comment: Comment = { id, nodeId: gid('Comment', `${repo.id}:${issue.number}:${id}`), body: typeof b.body === 'string' ? b.body : '', user: repo.owner, seq: nextSeq() };
        issue.comments.push(comment);
        sendJson(res, 201, { id, node_id: comment.nodeId, body: comment.body, user: userJson(repo.owner), created_at: FIXED_NOW, updated_at: FIXED_NOW, url: '', html_url: '' });
        return true;
      }
    }
    if (method === 'GET') { sendJson(res, 200, issueJson(repo, issue)); return true; }
    if (method === 'PATCH') {
      if (typeof b.title === 'string') issue.title = b.title;
      if (typeof b.body === 'string') issue.body = b.body;
      if (b.state === 'open' || b.state === 'closed') issue.state = b.state;
      if (Array.isArray(b.labels)) {
        const labels: Label[] = [];
        for (const l of b.labels as unknown[]) {
          const name = typeof l === 'string' ? l : (l as Record<string, unknown>)?.name;
          if (typeof name !== 'string') continue;
          const found = repo.labels.find((x) => x.name === name);
          if (!found) { errJson(res, 422, `Validation Failed: label "${name}" does not exist`); return true; }
          labels.push(found);
        }
        issue.labels = labels;
      }
      sendJson(res, 200, issueJson(repo, issue));
      return true;
    }
  }

  // Pull requests
  if (rest === '/pulls' && method === 'GET') {
    const state = q.get('state') ?? 'open';
    let list = repo.pulls.slice();
    if (state !== 'all') list = list.filter((p) => p.state === state);
    const direction = q.get('direction') ?? 'desc';
    list.sort((a, c) => (direction === 'asc' ? a.seq - c.seq : c.seq - a.seq));
    const { page, link } = paginate(list.map((p) => pullJson(repo, p)), q, req, `/api/v3/repos/${owner}/${repoName}/pulls`);
    sendJson(res, 200, page, link ? { link } : {});
    return true;
  }
  if (rest === '/pulls' && method === 'POST') {
    const title = typeof b.title === 'string' ? b.title : '';
    const head = typeof b.head === 'string' ? b.head.split(':').pop()! : '';
    const base = typeof b.base === 'string' ? b.base.split(':').pop()! : repo.defaultBranch;
    if (!refTip(repo, head) || !refTip(repo, base)) { errJson(res, 422, 'Validation Failed: head or base branch does not exist'); return true; }
    const number = repo.nextNumber;
    repo.nextNumber += 1;
    const id = nextGlobalId;
    nextGlobalId += 1;
    const pr: Pull = { id, nodeId: gid('PullRequest', `${repo.id}:${number}`), number, title, body: typeof b.body === 'string' ? b.body : '', state: 'open', merged: false, mergedAt: null, mergeSha: null, head, base, seq: nextSeq() };
    repo.pulls.push(pr);
    sendJson(res, 201, pullJson(repo, pr));
    return true;
  }
  const pullFilesMatch = rest.match(/^\/pulls\/(\d+)\/files$/);
  if (pullFilesMatch && method === 'GET') {
    const pr = repo.pulls.find((p) => p.number === parseInt(pullFilesMatch[1], 10));
    if (!pr) { errJson(res, 404, 'Not Found'); return true; }
    sendJson(res, 200, prFiles(repo, pr).map((f) => {
      const counts = lineCounts(repo, f);
      return {
        sha: f.newOid ?? f.oldOid ?? '', filename: f.path, status: f.status,
        additions: counts.additions, deletions: counts.deletions, changes: counts.additions + counts.deletions,
        blob_url: '', raw_url: '', contents_url: '', patch: '',
      };
    }));
    return true;
  }
  const pullMatch = rest.match(/^\/pulls\/(\d+)(\/merge)?$/);
  if (pullMatch) {
    const pr = repo.pulls.find((p) => p.number === parseInt(pullMatch[1], 10));
    if (!pr) { errJson(res, 404, 'Not Found'); return true; }
    if (pullMatch[2] === '/merge') {
      if (method !== 'PUT') { errJson(res, 404, 'Not Found'); return true; }
      if (pr.merged || pr.state === 'closed') { errJson(res, 405, 'Pull request is already closed'); return true; }
      if (prConflicted(repo, pr)) { errJson(res, 405, 'Merge conflict'); return true; }
      const commit = squashMerge(repo, pr);
      if (!commit) { errJson(res, 422, 'Validation Failed: cannot merge'); return true; }
      pr.merged = true;
      pr.state = 'closed';
      pr.mergedAt = FIXED_NOW;
      pr.mergeSha = commit.oid;
      sendJson(res, 200, { sha: commit.oid, merged: true, message: 'Pull request successfully merged' });
      return true;
    }
    if (method === 'GET') { sendJson(res, 200, pullJson(repo, pr)); return true; }
    if (method === 'PATCH') {
      if (typeof b.title === 'string') pr.title = b.title;
      if (typeof b.body === 'string') pr.body = b.body;
      if (b.state === 'closed') pr.state = 'closed';
      sendJson(res, 200, pullJson(repo, pr));
      return true;
    }
  }

  errJson(res, 404, 'Not Found');
  return true;
}
function dirListing(repo: Repo, files: Map<string, { oid: string; mode: string }>, dir: string): Record<string, unknown>[] {
  const prefix = dir === '' ? '' : `${dir}/`;
  const out: Record<string, unknown>[] = [];
  const seenDirs = new Set<string>();
  for (const [path, f] of files) {
    if (!path.startsWith(prefix)) continue;
    const restPath = path.slice(prefix.length);
    const slash = restPath.indexOf('/');
    if (slash < 0) {
      const data = getObject(repo, f.oid)?.data ?? Buffer.alloc(0);
      out.push({ type: 'file', name: restPath, path, sha: f.oid, size: data.length, url: '' });
    } else {
      const d = restPath.slice(0, slash);
      if (!seenDirs.has(d)) {
        seenDirs.add(d);
        out.push({ type: 'dir', name: d, path: `${prefix}${d}`, sha: '', size: 0, url: '' });
      }
    }
  }
  out.sort((a, c) => String(a.name) < String(c.name) ? -1 : 1);
  return out;
}

// ------------------------------------------------------------------ git fetch computation

function closureNoParents(repo: Repo, commits: Set<string>): Map<string, GitObject> {
  const out = new Map<string, GitObject>();
  const stack: string[] = [];
  for (const c of commits) {
    const obj = getObject(repo, c);
    if (!obj || obj.type !== 'commit') continue;
    out.set(c, obj);
    stack.push(parseCommit(obj.data).tree);
  }
  while (stack.length) {
    const oid = stack.pop()!;
    if (out.has(oid)) continue;
    const obj = getObject(repo, oid);
    if (!obj) continue;
    out.set(oid, obj);
    if (obj.type === 'tree') for (const e of parseTree(obj.data)) stack.push(e.oid);
    else if (obj.type === 'tag') {
      const m = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})/m);
      if (m) stack.push(m[1]);
    }
  }
  return out;
}
interface FetchPlan { objects: GitObject[]; shallow: string[]; unshallow: string[] }
function computeFetch(repo: Repo, wants: string[], haves: string[], shallowList: string[], depth: number | null): FetchPlan {
  const shallowSet = new Set(shallowList);
  const heldFull = haves.filter((h) => !shallowSet.has(h));
  const exclude = reachableObjects(repo, heldFull);
  const tagWants: GitObject[] = [];
  const wantCommits: string[] = [];
  for (const w of wants) {
    const obj = getObject(repo, w);
    if (!obj) continue;
    if (obj.type === 'tag') { tagWants.push(obj); wantCommits.push(peelToCommit(repo, w)); }
    else if (obj.type === 'commit') wantCommits.push(w);
  }
  const included = new Set<string>();
  if (depth != null) {
    const queue: [string, number][] = wantCommits.map((w) => [w, 0] as [string, number]);
    const seen = new Set<string>();
    while (queue.length) {
      const [oid, d] = queue.shift()!;
      if (seen.has(oid) || d >= depth) continue;
      seen.add(oid);
      const obj = getObject(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      included.add(oid);
      for (const p of parseCommit(obj.data).parents) queue.push([p, d + 1]);
    }
  } else {
    const stack = [...wantCommits];
    const seen = new Set<string>();
    while (stack.length) {
      const oid = stack.pop()!;
      if (seen.has(oid) || exclude.has(oid)) continue;
      seen.add(oid);
      const obj = getObject(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      included.add(oid);
      stack.push(...parseCommit(obj.data).parents);
    }
  }
  const objs = closureNoParents(repo, included);
  for (const t of tagWants) objs.set(t.oid, t);
  for (const k of exclude.keys()) objs.delete(k);
  // Never drop a wanted commit itself.
  for (const c of included) {
    const obj = getObject(repo, c);
    if (obj) objs.set(c, obj);
  }
  const shallow: string[] = [];
  for (const oid of included) {
    const obj = getObject(repo, oid);
    if (!obj) continue;
    const parents = parseCommit(obj.data).parents;
    if (parents.length === 0) continue;
    if (parents.some((p) => included.has(p))) continue;
    if (parents.some((p) => exclude.has(p))) continue;
    shallow.push(oid);
  }
  const unshallow: string[] = [];
  for (const b of shallowList) {
    const obj = getObject(repo, b);
    if (!obj || obj.type !== 'commit') continue;
    if (parseCommit(obj.data).parents.some((p) => included.has(p))) unshallow.push(b);
  }
  return { objects: [...objs.values()], shallow, unshallow };
}
function sidebandPackets(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 60000;
  for (let i = 0; i < pack.length; i += CHUNK) {
    const slice = pack.subarray(i, Math.min(pack.length, i + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (pack.length === 0) out.push(pktLine(Buffer.from([1])));
  return out;
}
function sortedRefs(repo: Repo): { name: string; oid: string }[] {
  const out = [...repo.refs.entries()].map(([name, oid]) => ({ name, oid }));
  out.sort((a, b) => (a.name < b.name ? -1 : 1));
  return out;
}
function headOid(repo: Repo): string {
  return repo.refs.get('refs/heads/main') ?? repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? ZERO_OID;
}

async function handleGit(req: IncomingMessage, res: ServerResponse, path: string, bodyBuf: Buffer): Promise<boolean> {
  const m = path.match(/^\/([^/]+)\/([^/]+)\.git(\/.*)$/);
  if (!m) return false;
  const method = req.method ?? 'GET';
  const owner = decodePath(m[1]);
  const repoName = decodePath(m[2]);
  const gitPath = m[3];
  if (!authOk(req)) { errJson(res, 401, 'Requires authentication'); return true; }
  learnViewer(owner);
  const repo = findRepo(owner, repoName);
  const isV2 = (req.headers['git-protocol'] ?? '') === 'version=2';

  if (method === 'GET' && gitPath.startsWith('/info/refs')) {
    const q = queryOf(req);
    const service = q.get('service') ?? '';
    if (!repo) { errJson(res, 404, 'Not Found'); return true; }
    if (service === 'git-upload-pack' && isV2) {
      const parts = [
        pktLine('# service=git-upload-pack\n'),
        pktLine('version 2\n'),
        pktLine('agent=makefun-forge/1.0\n'),
        pktLine('ls-refs=unborn\n'),
        pktLine('fetch=shallow\n'),
        pktLine('object-format=sha1\n'),
        PKT_FLUSH,
      ];
      sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-upload-pack') {
      const caps = 'multi_ack thin-pack side-band side-band-64k ofs-delta shallow deepen-since deepen-not deepen-relative no-progress include-tag multi_ack_detailed agent=makefun-forge/1.0 symref=HEAD:refs/heads/main';
      const parts: Buffer[] = [pktLine('# service=git-upload-pack\n')];
      parts.push(pktLine(`${headOid(repo)} HEAD\0${caps}\n`));
      for (const r of sortedRefs(repo)) {
        parts.push(pktLine(`${r.oid} ${r.name}\n`));
        const obj = getObject(repo, r.oid);
        if (obj && obj.type === 'tag') parts.push(pktLine(`${peelToCommit(repo, r.oid)} ${r.name}^{}\n`));
      }
      parts.push(PKT_FLUSH);
      sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-receive-pack') {
      const caps = 'report-status report-status-v2 side-band-64k delete-refs ofs-delta thin-pack symref=HEAD:refs/heads/main agent=makefun-forge/1.0';
      const parts: Buffer[] = [pktLine('# service=git-receive-pack\n')];
      parts.push(pktLine(`${headOid(repo)} HEAD\0${caps}\n`));
      for (const r of sortedRefs(repo)) {
        parts.push(pktLine(`${r.oid} ${r.name}\n`));
        const obj = getObject(repo, r.oid);
        if (obj && obj.type === 'tag') parts.push(pktLine(`${peelToCommit(repo, r.oid)} ${r.name}^{}\n`));
      }
      parts.push(PKT_FLUSH);
      sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-receive-pack-advertisement');
      return true;
    }
    errJson(res, 400, 'Unknown service');
    return true;
  }

  if (!repo) { errJson(res, 404, 'Not Found'); return true; }

  if (method === 'POST' && gitPath === '/git-upload-pack') {
    let packets: Pkt[];
    try { packets = parsePktLines(bodyBuf); } catch { errJson(res, 400, 'Malformed request'); return true; }
    const lines = packets.filter((p): p is { kind: 'data'; payload: Buffer } => p.kind === 'data').map((p) => p.payload.toString('utf8'));
    const command = lines.find((l) => l.startsWith('command='))?.slice('command='.length).trim() ?? '';
    if (isV2 && command === 'ls-refs') {
      const prefixes: string[] = [];
      for (const l of lines) if (l.startsWith('ref-prefix ')) prefixes.push(l.slice('ref-prefix '.length).trim());
      const out: Buffer[] = [];
      const includeHead = prefixes.length === 0 || prefixes.some((p) => 'HEAD'.startsWith(p));
      if (includeHead) {
        const head = headOid(repo);
        if (head === ZERO_OID) out.push(pktLine('unborn HEAD symref-target:refs/heads/main\n'));
        else out.push(pktLine(`${head} HEAD symref-target:refs/heads/main\n`));
      }
      for (const r of sortedRefs(repo)) {
        if (prefixes.length && !prefixes.some((p) => r.name.startsWith(p))) continue;
        const obj = getObject(repo, r.oid);
        let line = `${r.oid} ${r.name}`;
        if (obj && obj.type === 'tag') line += ` peeled:${peelToCommit(repo, r.oid)}`;
        out.push(pktLine(`${line}\n`));
      }
      out.push(PKT_FLUSH);
      sendRaw(res, 200, Buffer.concat(out), 'application/x-git-upload-pack-result');
      return true;
    }
    // Fetch (v2 command=fetch, or v0 wants/haves).
    const wants: string[] = [];
    const haves: string[] = [];
    const shallowReq: string[] = [];
    let depth: number | null = null;
    for (const l of lines) {
      const t = l.trim();
      if (t.startsWith('want ')) wants.push(t.slice(5).split(' ')[0]);
      else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
      else if (t.startsWith('shallow ')) shallowReq.push(t.slice(8).trim());
      else if (t.startsWith('deepen ')) { const n = parseInt(t.slice(7), 10); if (!Number.isNaN(n)) depth = n; }
    }
    const plan = computeFetch(repo, wants, haves, shallowReq, depth);
    const pack = encodePack(plan.objects);
    const acks = haves.filter((h) => wants.some((w) => {
      const wc = peelToCommit(repo, w);
      return isAncestor(repo, h, wc);
    }));
    if (isV2) {
      const parts: Buffer[] = [pktLine('acknowledgments\n')];
      if (acks.length) { for (const a of acks) parts.push(pktLine(`ACK ${a}\n`)); parts.push(pktLine('ready\n')); }
      else parts.push(pktLine('NAK\n'));
      parts.push(PKT_DELIM);
      if (plan.shallow.length || plan.unshallow.length) {
        parts.push(pktLine('shallow-info\n'));
        for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
        for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
        parts.push(PKT_DELIM);
      }
      parts.push(pktLine('packfile\n'));
      parts.push(...sidebandPackets(pack));
      parts.push(PKT_FLUSH);
      sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
      return true;
    }
    const parts: Buffer[] = [];
    if (acks.length) for (const a of acks) parts.push(pktLine(`ACK ${a}\n`));
    else parts.push(pktLine('NAK\n'));
    for (const s of plan.shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const s of plan.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
    parts.push(...sidebandPackets(pack));
    parts.push(PKT_FLUSH);
    sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-upload-pack-result');
    return true;
  }

  if (method === 'POST' && gitPath === '/git-receive-pack') {
    // Commands are pkt-lines up to the first flush; the rest is the pack.
    const commands: { oldOid: string; newOid: string; ref: string }[] = [];
    let pos = 0;
    let packStart = bodyBuf.length;
    let malformed = false;
    try {
      while (pos + 4 <= bodyBuf.length) {
        const lenHex = bodyBuf.subarray(pos, pos + 4).toString('ascii');
        if (lenHex === '0000') { pos += 4; packStart = pos; break; }
        if (lenHex === '0001') { pos += 4; continue; }
        const len = parseInt(lenHex, 16);
        if (Number.isNaN(len) || len < 4 || pos + len > bodyBuf.length) { malformed = true; break; }
        const text = bodyBuf.subarray(pos + 4, pos + len).toString('utf8');
        pos += len;
        const nul = text.indexOf('\0');
        const cmdText = nul >= 0 ? text.slice(0, nul) : text;
        const m2 = cmdText.trim().match(/^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/);
        if (!m2) { malformed = true; break; }
        commands.push({ oldOid: m2[1], newOid: m2[2], ref: m2[3] });
      }
    } catch { malformed = true; }
    if (malformed) { errJson(res, 400, 'Malformed request'); return true; }
    const packBytes = bodyBuf.subarray(packStart);
    let unpackOk = true;
    let unpackDetail = 'ok';
    if (packBytes.length >= 12) {
      try {
        const objects = decodePack(packBytes, (oid) => getObject(repo, oid));
        for (const o of objects) repo.objects.set(o.oid, o);
      } catch (e) {
        unpackOk = false;
        unpackDetail = e instanceof Error ? e.message : 'unpack failed';
      }
    }
    const reportLines: string[] = [unpackOk ? 'unpack ok\n' : `unpack ${unpackDetail}\n`];
    for (const cmd of commands) {
      if (!unpackOk) { reportLines.push(`ng ${cmd.ref} unpack failed\n`); continue; }
      const current = repo.refs.get(cmd.ref);
      if (cmd.newOid === ZERO_OID) {
        if (!current) reportLines.push(`ng ${cmd.ref} ref does not exist\n`);
        else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== current) reportLines.push(`ng ${cmd.ref} non-fast-forward\n`);
        else { repo.refs.delete(cmd.ref); reportLines.push(`ok ${cmd.ref}\n`); }
        continue;
      }
      const target = getObject(repo, cmd.newOid);
      if (!target) { reportLines.push(`ng ${cmd.ref} object not found\n`); continue; }
      if (cmd.oldOid === ZERO_OID) {
        if (current) reportLines.push(`ng ${cmd.ref} already exists\n`);
        else { repo.refs.set(cmd.ref, cmd.newOid); reportLines.push(`ok ${cmd.ref}\n`); }
        continue;
      }
      if (current !== cmd.oldOid) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
      const targetCommit = target.type === 'tag' ? peelToCommit(repo, cmd.newOid) : cmd.newOid;
      if (target.type !== 'tag' && target.type !== 'commit') { reportLines.push(`ng ${cmd.ref} invalid object\n`); continue; }
      if (!isAncestor(repo, cmd.oldOid, targetCommit)) { reportLines.push(`ng ${cmd.ref} non-fast-forward\n`); continue; }
      repo.refs.set(cmd.ref, cmd.newOid);
      reportLines.push(`ok ${cmd.ref}\n`);
    }
    const out: Buffer[] = [];
    for (const line of reportLines) out.push(pktLine(Buffer.concat([Buffer.from([1]), pktLine(line)])));
    out.push(PKT_FLUSH);
    sendRaw(res, 200, Buffer.concat(out), 'application/x-git-receive-pack-result');
    return true;
  }

  errJson(res, 404, 'Not Found');
  return true;
}

// ------------------------------------------------------------------ GraphQL v4

interface GqlValue { kind: 'variable' | 'int' | 'float' | 'string' | 'boolean' | 'null' | 'enum' | 'list' | 'object'; name?: string; value?: unknown; values?: GqlValue[]; fields?: { name: string; value: GqlValue }[] }
interface GqlField { alias: string | null; name: string; args: Record<string, GqlValue>; selections: GqlField[] | null }
interface GqlOperation { type: 'query' | 'mutation'; name: string | null; variables: Record<string, GqlValue | undefined>; selections: GqlField[] }

function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === ' ' || c === '\n' || c === '\r' || c === '\t' || c === ',') { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (src.startsWith('...', i)) { tokens.push('...'); i += 3; continue; }
    if ('{}()[]:!=$@&|'.includes(c)) { tokens.push(c); i += 1; continue; }
    if (c === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { const e = src[j + 1]; out += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e; j += 2; }
        else { out += src[j]; j += 1; }
      }
      tokens.push(JSON.stringify(out));
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i;
      while (j < src.length && /[0-9.eE+-]/.test(src[j])) j += 1;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    i += 1;
  }
  return tokens;
}
class GqlParser {
  private pos = 0;
  private tokens: string[];
  constructor(tokens: string[]) { this.tokens = tokens; }
  peek(): string | null { return this.tokens[this.pos] ?? null; }
  next(): string { return this.tokens[this.pos++]; }
  expect(t: string): void { if (this.next() !== t) throw new Error(`expected ${t}`); }
  parseValue(): GqlValue {
    const t = this.next();
    if (t === '$') return { kind: 'variable', name: this.next() };
    if (t === '[') {
      const values: GqlValue[] = [];
      while (this.peek() !== ']') values.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', values };
    }
    if (t === '{') {
      const fields: { name: string; value: GqlValue }[] = [];
      while (this.peek() !== '}') {
        const name = this.next();
        this.expect(':');
        fields.push({ name, value: this.parseValue() });
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (t.startsWith('"')) return { kind: 'string', value: JSON.parse(t) as string };
    if (t === 'true' || t === 'false') return { kind: 'boolean', value: t === 'true' };
    if (t === 'null') return { kind: 'null' };
    if (/^-?\d+$/.test(t)) return { kind: 'int', value: parseInt(t, 10) };
    if (/^-?[\d.]+$/.test(t)) return { kind: 'float', value: parseFloat(t) };
    return { kind: 'enum', value: t };
  }
  parseArguments(): Record<string, GqlValue> {
    const args: Record<string, GqlValue> = {};
    if (this.peek() !== '(') return args;
    this.expect('(');
    while (this.peek() !== ')') {
      const name = this.next();
      this.expect(':');
      args[name] = this.parseValue();
    }
    this.expect(')');
    return args;
  }
  skipDirectives(): void {
    while (this.peek() === '@') {
      this.next();
      this.next();
      if (this.peek() === '(') { this.parseArguments(); }
    }
  }
  parseSelections(): GqlField[] {
    this.expect('{');
    const out: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          const typeName = this.next();
          this.skipDirectives();
          const inner = this.parseSelections();
          for (const f of inner) out.push({ ...f, name: `...on:${typeName}:${f.name}` });
        } else {
          this.next(); // named fragment spread: skip (fragments defined inline are rare here)
        }
        continue;
      }
      let name = this.next();
      let alias: string | null = null;
      if (this.peek() === ':') { this.next(); alias = name; name = this.next(); }
      const args = this.parseArguments();
      this.skipDirectives();
      const selections = this.peek() === '{' ? this.parseSelections() : null;
      out.push({ alias, name, args, selections });
    }
    this.expect('}');
    return out;
  }
  parseDocument(): GqlOperation[] {
    const ops: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const t = this.peek();
      if (t === 'fragment') {
        this.next(); this.next();
        if (this.peek() === 'on') { this.next(); this.next(); }
        this.skipDirectives();
        this.parseSelections();
        continue;
      }
      let type: 'query' | 'mutation' = 'query';
      if (t === 'query' || t === 'mutation') { type = t as 'query' | 'mutation'; this.next(); }
      let name: string | null = null;
      if (this.peek() && this.peek() !== '{' && this.peek() !== '(') name = this.next();
      const variables: Record<string, GqlValue | undefined> = {};
      if (this.peek() === '(') {
        this.expect('(');
        while (this.peek() !== ')') {
          if (this.peek() === '$') { this.next(); const vn = this.next(); this.next(); // ':' then type name(s)
            while (this.peek() !== ')' && this.peek() !== '$' && this.peek() !== '=') this.next();
            if (this.peek() === '=') { this.next(); variables[vn] = this.parseValue(); } else variables[vn] = undefined;
          } else this.next();
        }
        this.expect(')');
      }
      this.skipDirectives();
      const selections = this.parseSelections();
      ops.push({ type, name, variables, selections });
    }
    return ops;
  }
}
function gqlResolve(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable': return variables[value.name ?? ''];
    case 'list': return (value.values ?? []).map((v) => gqlResolve(v, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const f of value.fields ?? []) out[f.name] = gqlResolve(f.value, variables);
      return out;
    }
    default: return value.value;
  }
}
function gqlArg(args: Record<string, GqlValue>, name: string, variables: Record<string, unknown>): unknown {
  const v = args[name];
  return v === undefined ? undefined : gqlResolve(v, variables);
}
const ISSUE_TYPE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'url', 'createdAt', 'author', 'labels', 'comments'];
const PR_TYPE_FIELDS = ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'title', 'body', 'url', 'createdAt'];
const REPO_TYPE_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'url', 'createdAt', 'isPrivate'];

interface GqlCtx { errors: { message: string }[] }
type GqlObj = { __type: string; repo?: Repo; issue?: Issue; pr?: Pull; comment?: Comment; user?: string; conn?: { items: unknown[]; endCursor: string | null; hasNextPage: boolean }; typeName?: string };

function findRepoById(id: number): Repo | null {
  for (const r of repos.values()) if (r.id === id) return r;
  return null;
}
function decodeGlobalId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const parts = text.split(':');
    if (parts.length < 2) return null;
    return { kind: parts[0], parts: parts.slice(1) };
  } catch { return null; }
}
function gqlCursor(n: number): string { return Buffer.from(`cursor:${n}`).toString('base64'); }
function gqlCursorNum(cursor: string): number | null {
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    const m = text.match(/^cursor:(\d+)$/);
    return m ? parseInt(m[1], 10) : null;
  } catch { return null; }
}

function gqlResolveField(ctx: GqlCtx, parent: GqlObj, field: GqlField, variables: Record<string, unknown>): unknown {
  const name = field.name;
  if (name === '__typename') return parent.__type;
  const type = parent.__type;
  // Inline fragment marker: field name was rewritten as ...on:Type:field
  if (name.startsWith('...on:')) {
    const [, fragType, realName] = name.split(':');
    if (fragType !== type) return null;
    return gqlResolveField(ctx, parent, { ...field, name: realName }, variables);
  }
  const unknown = (): null => { ctx.errors.push({ message: `Cannot query field "${name}" on type "${type}"` }); return null; };

  if (type === 'Query') {
    if (name === 'viewer') return { __type: 'User', user: viewer() };
    if (name === 'repository') {
      const owner = String(gqlArg(field.args, 'owner', variables) ?? '');
      const rname = String(gqlArg(field.args, 'name', variables) ?? '');
      if (owner) learnViewer(owner);
      const repo = findRepo(owner, rname);
      return repo ? { __type: 'Repository', repo } : null;
    }
    if (name === 'node') {
      const id = String(gqlArg(field.args, 'id', variables) ?? '');
      const decoded = decodeGlobalId(id);
      if (!decoded) return null;
      if (decoded.kind === 'Repository') {
        const repo = findRepoById(parseInt(decoded.parts[0], 10));
        return repo ? { __type: 'Repository', repo } : null;
      }
      if (decoded.kind === 'Issue') {
        const repo = findRepoById(parseInt(decoded.parts[0], 10));
        const issue = repo?.issues.find((i) => i.number === parseInt(decoded.parts[1], 10));
        return repo && issue ? { __type: 'Issue', repo, issue } : null;
      }
      if (decoded.kind === 'PullRequest') {
        const repo = findRepoById(parseInt(decoded.parts[0], 10));
        const pr = repo?.pulls.find((p) => p.number === parseInt(decoded.parts[1], 10));
        return repo && pr ? { __type: 'PullRequest', repo, pr } : null;
      }
      return null;
    }
    if (name === '__type') {
      const tname = String(gqlArg(field.args, 'name', variables) ?? '');
      return { __type: '__Type', typeName: tname };
    }
    return unknown();
  }
  if (type === 'Mutation') {
    const input = (gqlArg(field.args, 'input', variables) ?? {}) as Record<string, unknown>;
    if (name === 'createIssue') {
      const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
      const repo = decoded ? findRepoById(parseInt(decoded.parts[0], 10)) : null;
      if (!repo) return { issue: null };
      const number = repo.nextNumber; repo.nextNumber += 1;
      const id = nextGlobalId; nextGlobalId += 1;
      const issue: Issue = { id, nodeId: gid('Issue', `${repo.id}:${number}`), number, title: String(input.title ?? ''), body: typeof input.body === 'string' ? input.body : '', state: 'open', labels: [], comments: [], seq: nextSeq() };
      repo.issues.push(issue);
      return { issue: { __type: 'Issue', repo, issue } };
    }
    if (name === 'closeIssue') {
      const decoded = decodeGlobalId(String(input.issueId ?? ''));
      const repo = decoded ? findRepoById(parseInt(decoded.parts[0], 10)) : null;
      const issue = repo?.issues.find((i) => i.number === parseInt(decoded?.parts[1] ?? 'NaN', 10));
      if (!issue) return { issue: null };
      issue.state = 'closed';
      return { issue: { __type: 'Issue', repo: repo!, issue } };
    }
    if (name === 'createPullRequest') {
      const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
      const repo = decoded ? findRepoById(parseInt(decoded.parts[0], 10)) : null;
      if (!repo) return { pullRequest: null };
      const head = String(input.headRefName ?? '');
      const base = String(input.baseRefName ?? repo.defaultBranch);
      if (!refTip(repo, head) || !refTip(repo, base)) return { pullRequest: null };
      const number = repo.nextNumber; repo.nextNumber += 1;
      const id = nextGlobalId; nextGlobalId += 1;
      const pr: Pull = { id, nodeId: gid('PullRequest', `${repo.id}:${number}`), number, title: String(input.title ?? ''), body: typeof input.body === 'string' ? input.body : '', state: 'open', merged: false, mergedAt: null, mergeSha: null, head, base, seq: nextSeq() };
      repo.pulls.push(pr);
      return { pullRequest: { __type: 'PullRequest', repo, pr } };
    }
    if (name === 'mergePullRequest') {
      const decoded = decodeGlobalId(String(input.pullRequestId ?? ''));
      const repo = decoded ? findRepoById(parseInt(decoded.parts[0], 10)) : null;
      const pr = repo?.pulls.find((p) => p.number === parseInt(decoded?.parts[1] ?? 'NaN', 10));
      if (!repo || !pr) return { pullRequest: null };
      if (!pr.merged && pr.state === 'open' && !prConflicted(repo, pr)) {
        const commit = squashMerge(repo, pr);
        if (commit) { pr.merged = true; pr.state = 'closed'; pr.mergedAt = FIXED_NOW; pr.mergeSha = commit.oid; }
      }
      return { pullRequest: { __type: 'PullRequest', repo, pr } };
    }
    if (name === 'addComment') {
      const decoded = decodeGlobalId(String(input.subjectId ?? ''));
      const repo = decoded ? findRepoById(parseInt(decoded.parts[0], 10)) : null;
      const issue = repo?.issues.find((i) => i.number === parseInt(decoded?.parts[1] ?? 'NaN', 10));
      if (!repo || !issue) return { commentEdge: null };
      const id = nextGlobalId; nextGlobalId += 1;
      const comment: Comment = { id, nodeId: gid('Comment', `${repo.id}:${issue.number}:${id}`), body: String(input.body ?? ''), user: repo.owner, seq: nextSeq() };
      issue.comments.push(comment);
      return { commentEdge: { node: { __type: 'Comment', comment } } };
    }
    return unknown();
  }
  if (type === 'User') {
    if (name === 'login') return parent.user ?? viewer();
    if (name === 'id') return gid('User', parent.user ?? viewer());
    if (name === 'name') return parent.user ?? viewer();
    return unknown();
  }
  if (type === 'Repository') {
    const repo = parent.repo!;
    if (name === 'id') return repo.nodeId;
    if (name === 'databaseId') return repo.id;
    if (name === 'name') return repo.name;
    if (name === 'nameWithOwner') return `${repo.owner}/${repo.name}`;
    if (name === 'owner') return { __type: 'User', user: repo.owner };
    if (name === 'defaultBranchRef') return { __type: 'BranchRef', repo };
    if (name === 'viewerPermission') return 'ADMIN';
    if (name === 'hasIssuesEnabled') return true;
    if (name === 'description') return repo.description;
    if (name === 'isPrivate') return repo.isPrivate;
    if (name === 'url') return `https://example.invalid/${repo.owner}/${repo.name}`;
    if (name === 'createdAt') return FIXED_NOW;
    if (name === 'issue') {
      const n = gqlArg(field.args, 'number', variables) as number | undefined;
      const issue = repo.issues.find((i) => i.number === n);
      return issue ? { __type: 'Issue', repo, issue } : null;
    }
    if (name === 'issues') {
      const first = (gqlArg(field.args, 'first', variables) as number | undefined) ?? 100;
      const states = gqlArg(field.args, 'states', variables) as string[] | undefined;
      const orderBy = (gqlArg(field.args, 'orderBy', variables) ?? {}) as Record<string, unknown>;
      const after = gqlArg(field.args, 'after', variables) as string | undefined;
      let list = repo.issues.slice();
      if (states && states.length) list = list.filter((i) => states.includes(i.state === 'open' ? 'OPEN' : 'CLOSED'));
      const dir = String(orderBy.direction ?? 'ASC');
      list.sort((a, b) => (dir === 'DESC' ? b.number - a.number : a.number - b.number));
      if (after) {
        const cursorNum = gqlCursorNum(after);
        if (cursorNum !== null) list = list.filter((i) => (dir === 'DESC' ? i.number < cursorNum : i.number > cursorNum));
      }
      const page = list.slice(0, first);
      const hasNext = list.length > first;
      const endCursor = page.length ? gqlCursor(page[page.length - 1].number) : null;
      return { __type: 'IssueConnection', conn: { items: page.map((issue) => ({ __type: 'Issue', repo, issue })), endCursor, hasNextPage: hasNext } };
    }
    if (name === 'pullRequests') {
      const first = (gqlArg(field.args, 'first', variables) as number | undefined) ?? 100;
      const page = repo.pulls.slice(0, first);
      return { __type: 'PullRequestConnection', conn: { items: page.map((pr) => ({ __type: 'PullRequest', repo, pr })), endCursor: null, hasNextPage: repo.pulls.length > first } };
    }
    if (name === 'pullRequest') {
      const n = gqlArg(field.args, 'number', variables) as number | undefined;
      const pr = repo.pulls.find((p) => p.number === n);
      return pr ? { __type: 'PullRequest', repo, pr } : null;
    }
    return unknown();
  }
  if (type === 'BranchRef') {
    if (name === 'name') return parent.repo!.defaultBranch;
    return unknown();
  }
  if (type === 'Issue') {
    const issue = parent.issue!;
    if (name === 'id') return issue.nodeId;
    if (name === 'number') return issue.number;
    if (name === 'title') return issue.title;
    if (name === 'state') return issue.state === 'open' ? 'OPEN' : 'CLOSED';
    if (name === 'body') return issue.body;
    if (name === 'url') return `https://example.invalid/${parent.repo!.owner}/${parent.repo!.name}/issues/${issue.number}`;
    if (name === 'createdAt') return FIXED_NOW;
    if (name === 'author') return { __type: 'User', user: parent.repo!.owner };
    if (name === 'labels') return { __type: 'LabelConnection', conn: { items: issue.labels.map((l) => ({ __type: 'Label', label: l })), endCursor: null, hasNextPage: false } };
    if (name === 'comments') return { __type: 'CommentConnection', conn: { items: issue.comments.map((c) => ({ __type: 'Comment', comment: c })), endCursor: null, hasNextPage: false } };
    return unknown();
  }
  if (type === 'PullRequest') {
    const pr = parent.pr!;
    if (name === 'id') return pr.nodeId;
    if (name === 'number') return pr.number;
    if (name === 'title') return pr.title;
    if (name === 'body') return pr.body;
    if (name === 'state') return pr.merged ? 'MERGED' : pr.state === 'open' ? 'OPEN' : 'CLOSED';
    if (name === 'merged') return pr.merged;
    if (name === 'headRefName') return pr.head;
    if (name === 'baseRefName') return pr.base;
    if (name === 'mergeable') return prConflicted(parent.repo!, pr) ? 'CONFLICTING' : 'MERGEABLE';
    if (name === 'url') return `https://example.invalid/${parent.repo!.owner}/${parent.repo!.name}/pull/${pr.number}`;
    if (name === 'createdAt') return FIXED_NOW;
    if (name === 'files') {
      const first = (gqlArg(field.args, 'first', variables) as number | undefined) ?? 100;
      const files = prFiles(parent.repo!, pr).slice(0, first);
      return { __type: 'FileConnection', conn: { items: files.map((f) => ({ __type: 'ChangedFile', path: f.path })), endCursor: null, hasNextPage: false } };
    }
    return unknown();
  }
  if (type === 'IssueConnection' || type === 'PullRequestConnection' || type === 'FileConnection' || type === 'LabelConnection' || type === 'CommentConnection') {
    if (name === 'nodes') return parent.conn!.items;
    if (name === 'edges') return parent.conn!.items.map((node) => ({ __type: 'Edge', node }));
    if (name === 'pageInfo') return { __type: 'PageInfo', conn: parent.conn };
    if (name === 'totalCount') return parent.conn!.items.length;
    return unknown();
  }
  if (type === 'PageInfo') {
    if (name === 'hasNextPage') return parent.conn!.hasNextPage;
    if (name === 'endCursor') return parent.conn!.endCursor;
    if (name === 'hasPreviousPage') return false;
    if (name === 'startCursor') return parent.conn!.endCursor;
    return unknown();
  }
  if (type === 'Edge') {
    if (name === 'node') return (parent as unknown as { node: unknown }).node;
    if (name === 'cursor') return null;
    return unknown();
  }
  if (type === 'ChangedFile') {
    if (name === 'path') return (parent as unknown as { path: string }).path;
    return unknown();
  }
  if (type === 'Label') {
    const l = (parent as unknown as { label: Label }).label;
    if (name === 'name') return l.name;
    if (name === 'color') return l.color;
    return unknown();
  }
  if (type === 'Comment') {
    const c = parent.comment!;
    if (name === 'id') return c.nodeId;
    if (name === 'body') return c.body;
    return unknown();
  }
  if (type === '__Type') {
    const tname = parent.typeName ?? '';
    if (name === 'name') return tname;
    if (name === 'kind') return tname === 'SearchType' ? 'ENUM' : 'OBJECT';
    if (name === 'fields') {
      const list = tname === 'Issue' ? ISSUE_TYPE_FIELDS : tname === 'PullRequest' ? PR_TYPE_FIELDS : tname === 'Repository' ? REPO_TYPE_FIELDS : [];
      return list.map((n) => ({ __type: '__Field', fieldName: n }));
    }
    if (name === 'enumValues') {
      if (tname !== 'SearchType') return [];
      return ['ISSUE', 'REPOSITORY', 'USER'].map((n) => ({ __type: '__EnumValue', enumName: n }));
    }
    return unknown();
  }
  if (type === '__Field') {
    if (name === 'name') return (parent as unknown as { fieldName: string }).fieldName;
    return unknown();
  }
  if (type === '__EnumValue') {
    if (name === 'name') return (parent as unknown as { enumName: string }).enumName;
    return unknown();
  }
  return unknown();
}
function gqlExecuteSelections(ctx: GqlCtx, parent: GqlObj, selections: GqlField[], variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    const value = gqlResolveField(ctx, parent, field, variables);
    if (value === null || value === undefined) { out[key] = value ?? null; continue; }
    if (typeof value === 'object' && '__type' in (value as Record<string, unknown>)) {
      if (field.selections) out[key] = gqlExecuteSelections(ctx, value as GqlObj, field.selections, variables);
      else out[key] = value;
    } else if (Array.isArray(value)) {
      out[key] = value.map((v) => {
        if (v && typeof v === 'object' && '__type' in (v as Record<string, unknown>) && field.selections) return gqlExecuteSelections(ctx, v as GqlObj, field.selections, variables);
        return v;
      });
    } else if (typeof value === 'object' && field.selections) {
      // Plain object (mutation payload): walk its keys with sub-selections.
      const sub: Record<string, unknown> = {};
      for (const subField of field.selections) {
        const subVal = (value as Record<string, unknown>)[subField.name];
        if (subVal && typeof subVal === 'object' && '__type' in (subVal as Record<string, unknown>)) {
          sub[subField.alias ?? subField.name] = subField.selections ? gqlExecuteSelections(ctx, subVal as GqlObj, subField.selections, variables) : subVal;
        } else if (subVal && typeof subVal === 'object' && subField.selections) {
          sub[subField.alias ?? subField.name] = gqlExecuteSelections(ctx, { __type: 'Plain', ...(subVal as Record<string, unknown>) } as unknown as GqlObj, subField.selections, variables);
        } else {
          sub[subField.alias ?? subField.name] = subVal ?? null;
        }
      }
      out[key] = sub;
    } else {
      out[key] = value;
    }
  }
  return out;
}
function gqlExecute(doc: string, variables: Record<string, unknown>, operationName: string | null): { data: Record<string, unknown> | null; errors?: { message: string }[] } {
  const ctx: GqlCtx = { errors: [] };
  let ops: GqlOperation[];
  try {
    ops = new GqlParser(gqlTokenize(doc)).parseDocument();
  } catch (e) {
    return { data: null, errors: [{ message: e instanceof Error ? e.message : 'parse error' }] };
  }
  const op = operationName ? ops.find((o) => o.name === operationName) ?? ops[0] : ops[0];
  if (!op) return { data: null, errors: [{ message: 'no operation' }] };
  const vars: Record<string, unknown> = { ...variables };
  for (const [k, def] of Object.entries(op.variables)) if (vars[k] === undefined && def !== undefined) vars[k] = gqlResolve(def, variables);
  const rootType = op.type === 'mutation' ? 'Mutation' : 'Query';
  const data = gqlExecuteSelections(ctx, { __type: rootType }, op.selections, vars);
  const result: { data: Record<string, unknown> | null; errors?: { message: string }[] } = { data };
  if (ctx.errors.length) result.errors = ctx.errors;
  return result;
}

async function handleGraphql(req: IncomingMessage, res: ServerResponse, bodyBuf: Buffer): Promise<boolean> {
  if ((req.method ?? 'GET') !== 'POST') { errJson(res, 404, 'Not Found'); return true; }
  if (!authOk(req)) { sendJson(res, 401, { errors: [{ message: 'Requires authentication' }] }); return true; }
  const body = parseJsonBody(bodyBuf);
  if (!body.ok) { sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] }); return true; }
  const runOne = (doc: unknown): { data: Record<string, unknown> | null; errors?: { message: string }[] } => {
    const d = (doc ?? {}) as Record<string, unknown>;
    const query = typeof d.query === 'string' ? d.query : '';
    const variables = (d.variables ?? {}) as Record<string, unknown>;
    const operationName = typeof d.operationName === 'string' ? d.operationName : null;
    return gqlExecute(query, variables, operationName);
  };
  if (Array.isArray(body.value)) {
    sendJson(res, 200, body.value.map(runOne));
    return true;
  }
  sendJson(res, 200, runOne(body.value));
  return true;
}

// ------------------------------------------------------------------ MCP

const MCP_TOOLS: Record<string, unknown>[] = [
  { name: 'create_repo', description: 'Create a repository', inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] } },
  { name: 'get_repo', description: 'Get a repository by owner and name', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] } },
  { name: 'create_issue', description: 'Create an issue in a repository', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] } },
  { name: 'list_issues', description: 'List issues in a repository', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state: open, closed or all' } }, required: ['owner', 'repo'] } },
  { name: 'create_pull_request', description: 'Create a pull request', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' } }, required: ['owner', 'repo', 'title', 'head', 'base'] } },
  { name: 'merge_pull_request', description: 'Merge a pull request', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Repository owner' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'integer', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] } },
];
function mcpResult(res: ServerResponse, id: unknown, result: unknown): void {
  sendJson(res, 200, { jsonrpc: '2.0', id: id ?? null, result });
}
function mcpError(res: ServerResponse, id: unknown, code: number, message: string, status = 200): void {
  sendJson(res, status, { jsonrpc: '2.0', id: id ?? null, error: { code, message } });
}
function mcpToolResult(obj: unknown, isError = false): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj, isError };
}
function mcpRepoOf(args: Record<string, unknown>): Repo | null {
  const owner = typeof args.owner === 'string' ? args.owner : (typeof args.full_name === 'string' ? args.full_name.split('/')[0] : viewer());
  const name = typeof args.repo === 'string' ? args.repo : (typeof args.full_name === 'string' ? args.full_name.split('/').slice(1).join('/') : '');
  if (owner && name) {
    const repo = findRepo(owner, name);
    if (repo) learnViewer(owner);
    return repo;
  }
  return null;
}
async function handleMcp(req: IncomingMessage, res: ServerResponse, bodyBuf: Buffer): Promise<void> {
  if ((req.method ?? 'GET') !== 'POST') { errJson(res, 404, 'Not Found'); return; }
  const parsed = parseJsonBody(bodyBuf);
  if (!parsed.ok) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const msg = (parsed.value ?? {}) as Record<string, unknown>;
  const id = msg.id ?? null;
  if (!authOk(req)) {
    mcpError(res, id, -32001, 'Requires authentication', 401);
    return;
  }
  const method = typeof msg.method === 'string' ? msg.method : '';
  const params = (msg.params ?? {}) as Record<string, unknown>;
  if (method === 'server/discover') {
    mcpResult(res, id, {
      protocolVersion: '2026-07-28',
      supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
      serverInfo: { name: 'makefun-forge', version: '1.0.0' },
      capabilities: { tools: {} },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'makefun-forge', version: '1.0.0' } },
    });
    return;
  }
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    const known = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
    mcpResult(res, id, {
      protocolVersion: known.includes(requested) ? requested : '2025-11-25',
      capabilities: { tools: {} },
      serverInfo: { name: 'makefun-forge', version: '1.0.0' },
    });
    return;
  }
  if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': `req-${nextSeq()}` });
    res.end();
    return;
  }
  if (method === 'ping') { mcpResult(res, id, {}); return; }
  if (method === 'tools/list') {
    mcpResult(res, id, { tools: MCP_TOOLS });
    return;
  }
  if (method === 'tools/call') {
    const name = typeof params.name === 'string' ? params.name : '';
    const args = (params.arguments ?? {}) as Record<string, unknown>;
    const tool = MCP_TOOLS.find((t) => t.name === name);
    if (!tool) { mcpError(res, id, -32601, `Unknown tool: ${name}`); return; }
    const schema = (tool.inputSchema ?? {}) as Record<string, unknown>;
    const required = (schema.required ?? []) as string[];
    for (const key of required) {
      if (args[key] === undefined || args[key] === null || args[key] === '') {
        mcpResult(res, id, mcpToolResult({ error: `missing required argument: ${key}` }, true));
        return;
      }
    }
    const fullName = typeof args.full_name === 'string' ? args.full_name : '';
    if (name === 'create_repo') {
      const rname = String(args.name ?? '');
      let repo = repos.get(rname) ?? null;
      if (!repo) repo = createRepo(rname, typeof args.description === 'string' ? args.description : '', args.private === true);
      mcpResult(res, id, mcpToolResult(repoJson(repo)));
      return;
    }
    if (name === 'get_repo') {
      const repo = mcpRepoOf(args);
      if (!repo) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      mcpResult(res, id, mcpToolResult(repoJson(repo)));
      return;
    }
    if (name === 'create_issue') {
      const repo = mcpRepoOf(args);
      if (!repo) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      const number = repo.nextNumber; repo.nextNumber += 1;
      const gidNum = nextGlobalId; nextGlobalId += 1;
      const issue: Issue = { id: gidNum, nodeId: gid('Issue', `${repo.id}:${number}`), number, title: String(args.title ?? ''), body: typeof args.body === 'string' ? args.body : '', state: 'open', labels: [], comments: [], seq: nextSeq() };
      repo.issues.push(issue);
      mcpResult(res, id, mcpToolResult(issueJson(repo, issue)));
      return;
    }
    if (name === 'list_issues') {
      const repo = mcpRepoOf(args);
      if (!repo) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      const state = typeof args.state === 'string' ? args.state : 'open';
      let list = repo.issues.slice();
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b) => a.seq - b.seq);
      const out = { issues: list.map((i) => issueJson(repo, i)) };
      mcpResult(res, id, mcpToolResult(out));
      return;
    }
    if (name === 'create_pull_request') {
      const repo = mcpRepoOf(args);
      if (!repo) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      const head = String(args.head ?? '');
      const base = String(args.base ?? repo.defaultBranch);
      if (!refTip(repo, head) || !refTip(repo, base)) { mcpResult(res, id, mcpToolResult({ error: 'head or base branch does not exist' }, true)); return; }
      const number = repo.nextNumber; repo.nextNumber += 1;
      const gidNum = nextGlobalId; nextGlobalId += 1;
      const pr: Pull = { id: gidNum, nodeId: gid('PullRequest', `${repo.id}:${number}`), number, title: String(args.title ?? ''), body: typeof args.body === 'string' ? args.body : '', state: 'open', merged: false, mergedAt: null, mergeSha: null, head, base, seq: nextSeq() };
      repo.pulls.push(pr);
      mcpResult(res, id, mcpToolResult(pullJson(repo, pr)));
      return;
    }
    if (name === 'merge_pull_request') {
      const repo = mcpRepoOf(args);
      if (!repo) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      const number = typeof args.pull_number === 'number' ? args.pull_number : parseInt(String(args.pull_number ?? ''), 10);
      const pr = repo.pulls.find((p) => p.number === number);
      if (!pr) { mcpResult(res, id, mcpToolResult({ error: 'Not Found' }, true)); return; }
      if (pr.merged || pr.state === 'closed') { mcpResult(res, id, mcpToolResult({ error: 'Pull request is already closed' }, true)); return; }
      if (prConflicted(repo, pr)) { mcpResult(res, id, mcpToolResult({ error: 'Merge conflict' }, true)); return; }
      const commit = squashMerge(repo, pr);
      if (!commit) { mcpResult(res, id, mcpToolResult({ error: 'cannot merge' }, true)); return; }
      pr.merged = true; pr.state = 'closed'; pr.mergedAt = FIXED_NOW; pr.mergeSha = commit.oid;
      mcpResult(res, id, mcpToolResult({ sha: commit.oid, merged: true, number: pr.number, message: 'Pull request successfully merged' }));
      return;
    }
    void fullName;
    mcpError(res, id, -32602, `Tool not implemented: ${name}`);
    return;
  }
  mcpError(res, id, -32601, `Method not found: ${method}`);
}

// ------------------------------------------------------------------ server

/** Build the server. It binds nothing until the caller listens; the entry listens on an ephemeral port. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const path = pathOf(req);
        const method = req.method ?? 'GET';
        if (method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
        const bodyBuf = (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE')
          ? await readBody(req)
          : Buffer.alloc(0);
        if (path === '/mcp') { await handleMcp(req, res, bodyBuf); return; }
        if (path === '/api/graphql') { await handleGraphql(req, res, bodyBuf); return; }
        if (path.startsWith('/api/v3')) { await handleRest(req, res, path, bodyBuf); return; }
        if (await handleGit(req, res, path, bodyBuf)) return;
        sendJson(res, 404, { message: 'Not Found' });
      } catch (e) {
        if (!res.headersSent) sendJson(res, 500, { message: e instanceof Error ? e.message : 'Internal Server Error' });
        else { try { res.end(); } catch { /* already closed */ } }
      }
    })();
  });
}
