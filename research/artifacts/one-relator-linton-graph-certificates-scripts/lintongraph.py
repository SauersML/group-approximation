#!/usr/bin/env python3
"""lintongraph.py -- Linton certificates for HNN extensions of free groups along f.g. subgroups.

Input: K = F(1..r), A = <g_1..g_m>, B = <h_1..h_m> free on these generators, psi(g_i) = h_i,
G = <K, t | t a t^-1 = psi(a)>.  Computes, following M. Linton, One-relator hierarchies,
arXiv:2202.11324v3 (Section 6):
  * stabilisers of geodesic segments of the Bass-Serre tree with an endpoint at K, up to
    K-conjugacy, by Stab(S) ~ psi(A cap P^h) or psi^-1(B cap P^h) over shorter P (Stallings
    pullbacks; a back-turn excludes the base component, i.e. h in A resp. B);
  * sZ(psi) and sZ(psi^-1) from the pure-direction states (definition p. 23);
  * the vertex set of the graph of cyclic stabilisers (p. 27): A-classes of maximal cyclic
    subgroups of A containing a nontrivial cyclic A cap Stab(S)^h, likewise for B, over all
    segments up to length max sZ + 1;
  * its edges read literally from p. 27 (H-edges: nontrivial powers K-conjugate; t-edges:
    h in A t^-1 B u B t A, i.e. nu(w)^k in A with psi(nu(w)^k) B-conjugate to a power of nu(v),
    or the same through B and psi^-1).  Extra H-edges between distinct vertices of one part are
    kept (the condition h notin <nu(v)><nu(w)> is ignored), so the edge set is a superset;
  * loops, and whether a cyclically alternating closed path of length >= 2 exists.
Verdict PASS: sZ finite, no loop of either type, no alternating closed path.
Modes: lintongraph.py calib | census L | words FILE
"""
import sys, math
from collections import deque, defaultdict
import census as C
import census2 as C2
import malnormal as M
import os
VERBOSE = bool(os.environ.get('LG_VERBOSE'))

def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return tuple(out)
def inv(w): return tuple(-x for x in reversed(w))
def mul(*ws): return red([x for w in ws for x in w])

class Graph:
    """Folded pointed Stallings graph (base 0). track=True: edge labels in the generators, so a
    closed path at 0 spells its element as a word in the generators (type I folds only)."""
    def __init__(self, gens, track=False):
        E, nv = [], 1
        for i, g in enumerate(gens):
            g, cur = red(g), 0
            for j, x in enumerate(g):
                nxt = 0 if j == len(g) - 1 else nv
                if j < len(g) - 1: nv += 1
                lab = ((i + 1,) if x > 0 else (-(i + 1),)) if (track and j == 0) else ()
                E.append([cur, x, nxt, lab] if x > 0 else [nxt, -x, cur, lab])
                cur = nxt
        self.track = track
        E = self._fold(E)
        verts = sorted({e[0] for e in E} | {e[2] for e in E} | {0})
        ren = {v: i for i, v in enumerate(verts)}
        self.E = [[ren[e[0]], e[1], ren[e[2]], e[3]] for e in E]
        self.nv = len(verts)
        self.out = {(e[0], e[1]): e for e in self.E}
        self.inn = {(e[2], e[1]): e for e in self.E}
        self.adj = defaultdict(list)
        for e in self.E:
            self.adj[e[0]].append((e[1], e[2])); self.adj[e[2]].append((-e[1], e[0]))
        self.tw, q = {0: ()}, deque([0])
        while q:
            v = q.popleft()
            for a, w in sorted(self.adj[v]):
                if w not in self.tw: self.tw[w] = self.tw[v] + (a,); q.append(w)

    def _fold(self, E):
        while True:
            seen, hit = {}, None
            for idx, e in enumerate(E):
                for key in ((e[0], e[1], 'o'), (e[2], e[1], 'i')):
                    if key in seen: hit = (seen[key], idx, key[2]); break
                    seen[key] = idx
                if hit: break
            if not hit: return E
            i1, i2, kind = hit
            e1, e2 = E[i1], E[i2]
            if e1[0] == e2[0] and e1[2] == e2[2]:
                if self.track and e1[3] != e2[3]:
                    raise ValueError('type II fold: generators are not a free basis')
                del E[i2]; continue
            if kind == 'o':
                if e2[2] == 0: e1, e2 = e2, e1
                x, y, s = e2[2], e1[2], mul(inv(e2[3]), e1[3])
            else:
                if e2[0] == 0: e1, e2 = e2, e1
                x, y, s = e2[0], e1[0], mul(e2[3], inv(e1[3]))
            if self.track and s:
                for e in E:
                    if e[0] == x and e[2] == x: e[3] = mul(inv(s), e[3], s)
                    elif e[0] == x: e[3] = mul(inv(s), e[3])
                    elif e[2] == x: e[3] = mul(e[3], s)
            for e in E:
                if e[0] == x: e[0] = y
                if e[2] == x: e[2] = y

    def read(self, w, start=0):
        v, lab = start, []
        for x in w:
            e = self.out.get((v, x)) if x > 0 else self.inn.get((v, -x))
            if e is None: return None, None
            if x > 0: v = e[2]; lab.extend(e[3])
            else: v = e[0]; lab.extend(inv(e[3]))
        return v, red(lab)
    def member(self, w): return self.read(red(w))[0] == 0
    def express(self, w):
        v, lab = self.read(red(w)); assert v == 0, 'not a member'; return lab
    def rank(self): return len(self.E) - self.nv + 1
    def key(self):
        order, q = {0: 0}, deque([0])
        while q:
            v = q.popleft()
            for a, w in sorted(self.adj[v]):
                if w not in order: order[w] = len(order); q.append(w)
        return tuple(sorted((order[e[0]], e[1], order[e[2]]) for e in self.E))

def pullback(G1, G2):
    """Positive-rank components of the fibre product: (rank, contains_base, gens), gens as
    elements of K1 (loops at the representative, conjugated by its tree word in G1)."""
    by = defaultdict(list)
    for f in G2.E: by[f[1]].append(f)
    PE = [((e[0], f[0]), e[1], (e[2], f[2])) for e in G1.E for f in by[e[1]]]
    adj = defaultdict(list)
    for (u, a, v) in PE: adj[u].append((a, v)); adj[v].append((-a, u))
    seen, comps = set(), []
    for s in ([(0, 0)] if (0, 0) in adj else []) + sorted(adj):
        if s in seen: continue
        comp, q = {s: ()}, deque([s]); seen.add(s)
        while q:
            u = q.popleft()
            for a, v in sorted(adj[u]):
                if v not in comp: comp[v] = comp[u] + (a,); seen.add(v); q.append(v)
        E = [(u, a, v) for (u, a, v) in PE if u in comp]
        r = len(E) - len(comp) + 1
        if r < 1: continue
        al = G1.tw[s[0]]
        gens = [red(al + g + inv(al)) for g in (red(comp[u] + (a,) + inv(comp[v])) for (u, a, v) in E) if g]
        comps.append((r, s == (0, 0), gens))
    return comps

def root(g):
    g = red(g); i = 0
    while i < len(g) // 2 and g[i] == -g[-1 - i]: i += 1
    s, c = g[:i], g[i:len(g) - i]
    p = C.min_period(list(c))
    return s, c[:p], len(c) // p

def cyc_key(c0):
    cands = [c0[k:] + c0[:k] for k in range(len(c0))]
    ic = inv(c0); cands += [ic[k:] + ic[:k] for k in range(len(ic))]
    return min(cands)

def orbit_return(G, v, c0):
    u, e = v, 0
    while True:
        u, _ = G.read(c0, u); e += 1
        if u is None or e > G.nv + 1: return None
        if u == v: return e

def part_class(G, g):
    """(generator of the maximal cyclic subgroup of the subgroup of G containing g, its key)."""
    s, c0, k = root(g)
    v, _ = G.read(s)
    e = orbit_return(G, v, c0) if v is not None else None
    if e is None: return None
    loop = c0 * e
    cands = []
    for w in (loop, inv(loop)):
        for k2 in range(len(w)):
            cands.append((G.read(w[:k2], v)[0], w[k2:] + w[:k2]))
    return red(s + loop + inv(s)), min(cands)

def power_in(G, g):
    """smallest power g^d lying in the subgroup of G (g != 1), or None."""
    s, c0, k = root(g)
    v, _ = G.read(s)
    e = orbit_return(G, v, c0) if v is not None else None
    if e is None: return None
    d = e // math.gcd(e, k)
    return red(s + c0 * (k * d) + inv(s))

def certify(r, Agens, Bgens, extra=1, dmax=10):
    GA, GB = Graph(Agens, True), Graph(Bgens, True)
    info = {'rankA': GA.rank(), 'rankB': GB.rank()}
    if not (GA.rank() == len(Agens) == GB.rank() == len(Bgens)):
        return 'FAIL(edge groups not free on the given generators)', info
    def psi(x, fwd):
        G, img = (GA, Bgens) if fwd else (GB, Agens)
        return red([y for i in G.express(x) for y in (img[i - 1] if i > 0 else inv(img[-i - 1]))])
    sz = {'f': 1, 'b': 1}
    verts, vdepth = {}, {}
    frontier, mixed_noncyclic = [('H', tuple((i,) for i in range(1, r + 1)), 'n')], 0
    depth = 0
    while True:
        depth += 1
        if depth > dmax: return 'FAIL(depth cap %d: not certified Z-stable)' % dmax, info
        nxt = {}
        for flag, gens, pur in frontier:
            GX = Graph(gens)
            for d, GP, excl in (('f', GA, flag == 'A'), ('b', GB, flag == 'B')):
                for rk, base, lg in pullback(GP, GX):
                    if excl and base: continue
                    X2 = tuple(psi(y, d == 'f') for y in lg)
                    pur2 = d if pur in ('n', d) else 'm'
                    k2 = ('B' if d == 'f' else 'A', Graph(X2).key(), pur2)
                    if k2 not in nxt: nxt[k2] = (k2[0], X2, pur2, rk)
        frontier = []
        for flag, X2, pur2, rk in nxt.values():
            if VERBOSE: print('  STATE depth=%d flag=%s pur=%s rank=%d gens=%s' % (depth, flag, pur2, rk, [wstr(z, r) for z in X2]))
            if rk >= 2:
                if pur2 in ('f', 'b'): sz[pur2] = max(sz[pur2], depth + 1)
                else: mixed_noncyclic += 1
            frontier.append((flag, X2, pur2))
            GX = Graph(X2)
            for part, GP in (('A', GA), ('B', GB)):
                for rk2, base, lg in pullback(GP, GX):
                    if rk2 != 1: continue
                    pc = part_class(GP, lg[0])
                    key = (part, pc[1])
                    if VERBOSE: print('    VERTEX part=%s from g=%s nu=%s new=%s' % (part, wstr(lg[0], r), wstr(pc[0], r), key not in verts))
                    if key not in verts: verts[key], vdepth[key] = pc[0], depth
        if depth >= max(sz.values()) + extra and all(rk < 2 for (_, _, _, rk) in nxt.values()):
            break
    info.update(sZ=(sz['f'], sz['b']), depth=depth, mixed_noncyclic=mixed_noncyclic,
                late=[k for k in verts if vdepth[k] > max(sz.values())])
    V = sorted(verts)
    nu = {v: verts[v] for v in V}
    rootkey = {v: cyc_key(root(nu[v])[1]) for v in V}
    Hed, ted, hloops, tloops = set(), set(), [], []
    for i, v in enumerate(V):
        if root(nu[v])[2] >= 2: hloops.append(v)
        for w in V[i + 1:]:
            if rootkey[v] == rootkey[w]: Hed.add((v, w))
    for w in V:
        for (GP, GQ, fwd) in ((GA, GB, True), (GB, GA, False)):
            x = power_in(GP, nu[w])
            if x is None: continue
            img = part_class(GQ, psi(x, fwd))
            for v in V:
                y = power_in(GQ, nu[v])
                if y is None: continue
                if part_class(GQ, y)[1] == img[1]:
                    if v == w: tloops.append(v)
                    else: ted.add(tuple(sorted((v, w))))
    arcs = defaultdict(list)
    for T, E in (('H', Hed | {(v, v) for v in hloops}), ('t', ted | {(v, v) for v in tloops})):
        for v, w in E:
            for a, b in ((v, w), (w, v)):
                arcs[(a, 'H' if T == 't' else 't')].append((b, T))
    cyc = find_cycle(arcs)
    info.update(V=[(v[0], nu[v]) for v in V], H=len(Hed), t=len(ted), hloops=len(hloops),
                tloops=len(tloops), cycle=cyc)
    if info['late']: return 'FAIL(vertices appeared beyond depth sZ)', info
    if tloops: return 'FAIL(t-loop)', info
    if cyc: return 'FAIL(alternating cycle)', info
    if hloops: return 'PASS_HLOOP', info
    return 'PASS', info

def find_cycle(arcs):
    nodes = set(arcs) | {b for l in arcs.values() for b in l}
    color, stack = {n: 0 for n in nodes}, []
    for s in sorted(nodes, key=str):
        if color[s]: continue
        it = [(s, iter(arcs.get(s, [])))]; color[s] = 1; stack = [s]
        while it:
            u, g = it[-1]
            nxtn = next(g, None)
            if nxtn is None:
                color[u] = 2; it.pop(); stack.pop(); continue
            if color[nxtn] == 1: return stack[stack.index(nxtn):] + [nxtn]
            if color[nxtn] == 0:
                color[nxtn] = 1; stack.append(nxtn); it.append((nxtn, iter(arcs.get(nxtn, []))))
    return None

def wstr(w, r):
    if r == 2: return ''.join({1: 'x', -1: 'X', 2: 'y', -2: 'Y'}[z] for z in w) or '1'
    return '.'.join(('a%d' % z) if z > 0 else ('A%d' % -z) for z in w) or '1'

def run_seq(cs):
    fp = M.free_piece(cs)
    if fp is None: return 'NONFREE', None
    if C.extremes(cs)[2] != 1: return 'GCD', None
    u, r, Fm, Fp = fp
    return certify(r, [tuple(z) for z in Fm], [tuple(z) for z in Fp]) + ((u, r),)

def report(tag, w, verdict, info, ur):
    u, r = ur
    V = ' '.join('%s:%s' % (p, wstr(n, r)) for p, n in info.get('V', []))
    print('VERDICT %s %s rank=%d u=%s sZ=%s depth=%s mixed_nc=%s V=[%s] H=%s t=%s hloops=%s tloops=%s cycle=%s -> %s'
          % (tag, w, r, wstr(u, r), info.get('sZ'), info.get('depth'), info.get('mixed_noncyclic'), V,
             info.get('H'), info.get('t'), info.get('hloops'), info.get('tloops'),
             bool(info.get('cycle')), verdict), flush=True)

def main():
    mode = sys.argv[1]
    if mode == 'calib':
        y = (-2, -2, 1, 1, -2, -2)
        v, info = certify(2, [(1,), y], [y, (2,)])
        report('CAL-linton-ex1.2', 'z2yz2X2', v, info, ((), 2))
        v, info = certify(2, [(-2, 1, 1, 1, 2)], [(-1, -1)])
        report('CAL-linton-ex6.12-BS(2,-3)', 'y2zxZyzxZ', v, info, ((), 2))
    elif mode == 'census':
        L = int(sys.argv[2]); seen = set()
        for seq in C.gen(L):
            m, n, g, top, bot = C.extremes(seq)
            if C.peelable(top) or C.peelable(bot): continue
            c = C.canon(seq)
            if c in seen: continue
            seen.add(c); cs = list(c); w = C.seq_to_word(cs)
            if C.min_period(w) < len(w): continue
            C.BUDGET[0] = 3000
            if C.cert_word(w, 0)[0]: continue
            pp = C2.pp_search(w, 4, 20000) is not None
            res = run_seq(cs)
            if res[1] is None: print('VERDICT SEQ%d %s %s pp=%s' % (L, C.word_str(w), res[0], pp)); continue
            report('SEQ%d pp=%s' % (L, pp), C.word_str(w), *res)
    elif mode == 'words':
        code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
        for line in open(sys.argv[2]):
            f = line.split()
            if len(f) < 2 or f[0] not in ('REST', 'CLASS'): continue
            wtxt = f[1]
            if f[0] == 'CLASS' and not line.rstrip().endswith('REST'): continue
            w = [code[ch] for ch in wtxt]
            p, q = C.expsums(w)
            phis = [(q // math.gcd(p, q), -p // math.gcd(p, q))] if (p, q) != (0, 0) else C.small_phis()
            best = None
            for x, yy in phis:
                seq = C.magnus(C.adapt(list(w), x, yy))
                if seq is None: continue
                cs = list(C.canon(seq))
                res = run_seq(cs)
                if res[1] is None:
                    best = best or ('WORDS', C.word_str(C.seq_to_word(cs)), res[0]); continue
                report('WORDS phi=%d,%d' % (x, yy), wtxt, *res)
                if res[0].startswith('PASS'): best = None; break
                best = 'reported'
            if best not in (None, 'reported'): print('VERDICT %s %s via %s %s' % (best[0], wtxt, best[1], best[2]))
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
