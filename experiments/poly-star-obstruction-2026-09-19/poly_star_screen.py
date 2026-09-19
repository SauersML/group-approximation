#!/usr/bin/env python3
"""Screen for `unit-weight-polynomial-recursions-split-over-loop-edges`.

Three-letter M_11 families (chain, fan, two-letter section cycle, signed cycle), all fully
self-replicating by Lemma S (the letter s has support {0,1,2,3} with alpha at 1, beta at 2).
For each recursion the script decides exactly:
  (U)      unit weight (by construction, rechecked);
  (Poly)   every strongly connected component of the signed weight-preserving digraph is one
           directed cycle; p = lcm of the cycle lengths;
  (L1_p)   at level p every cycle letter has exactly one self-loop (Rec.loop_states(p));
  degrees  deg(cycle SCC) = 1 + max deg below, deg(non-cycle) = max deg below, rooted = -1;
  D        letters reachable from a cycle letter after leaving its cycle;
  per component Lam of the level-p loop graph Delta_p:
    E_Lam = cycle letters of Lam lying in D                  (edge sub-basis);
    (a)    the edge group rho(F(E_Lam)) contains no conjugate of iota_y(G'):
           a1: |E_Lam| <= 1 (cyclic), or
           a2: every E_Lam letter has degree < top and some [x, s] (x in {a, e}, s a top-degree
               cycle letter) has a level-1 section c s'^(+-1) d, s' top-degree cycle letter;
    free   alternatively: the E_Lam edges form a forest in Lam and rank(Lam) <= 1; then Lam
           contributes the leaf C_c (cyclic or trivial) with an empty edge, and (a), (b) are
           not needed for Lam;
    (b)    rho(V_Lam) != G: Lam has no top-degree letter, or the root image of its loops is
           proper in M_11, or <loops> is intransitive on level 2 or 3;
  (N)      every level-p loop is nontrivial in G.
Verdicts: 'bounded' (all degrees 0: contracting), 'star' (killed by the star obstruction, with
the sufficient conditions used), or 'survivor' with the failing condition.  For the first 12
survivors per family the level-2 image of <loops> is computed (sympy Schreier-Sims) and
compared with M_11 wr M_11 (order 7920^12).
Default sub-family: decorations in {"", a} (4096 recursions per family); --full uses 5^3.
Run (needs loopgraph.py from ../loop-graph-screen-2026-09-18 on the path):
  nice -n 10 timeout 1200 python3 poly_star_screen.py FAMILY >> poly_star_screen.out
"""
import itertools, sys, os
from math import lcm
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'loop-graph-screen-2026-09-18'))
from loopgraph import N, ID, ALPHA, BETA, W, reduce, inv, fmt, pmul, pinv, Rec

ROOT = {"a": ALPHA, "e": BETA}
PERMWORDS = ["a", "e", "a e", "a E", "A e", "e a", "a a", "e e"]
DECOS = ["", "a"]          # default sub-family; --full uses ["", "a", "A", "e", "E"]
DECOS_FULL = ["", "a", "A", "e", "E"]
ORDB = 60

def pw(s):
    return Rec("_", ROOT, {}).perm(W(s)) if s else ID

def group_order(gens, cap=8000):
    seen, todo = {ID}, [ID]
    while todo:
        p = todo.pop()
        for g in gens:
            q = pmul(p, g)
            if q not in seen:
                seen.add(q); todo.append(q)
                if len(seen) > cap: return len(seen)
    return len(seen)

def w(s): return W(s) if s else ()

def family(kind, ps, pt, pu, A, C, E):
    """kind in chain, fan, cycle, scycle.  Returns a Rec."""
    st = {}
    if kind == "chain":   # s -> t -> u, all loop at 0
        st["s"] = (ps, {0: w(A + " s"), 1: W("a"), 2: W("e"), 3: W("t")})
        st["t"] = (pt, {0: w(C + " t"), 4: W("a"), 5: W("u")})
        st["u"] = (pu, {0: w(E + " u"), 6: W("a")})
    elif kind == "fan":   # s -> t <- u
        st["s"] = (ps, {0: w(A + " s"), 1: W("a"), 2: W("e"), 3: W("t")})
        st["t"] = (pt, {0: w(C + " t"), 4: W("a")})
        st["u"] = (pu, {0: w(E + " u"), 5: W("a"), 6: W("t")})
    elif kind in ("cycle", "scycle"):   # s <-> t (no self-loops), exit s -> u
        st["s"] = (ps, {0: w(A + " t"), 1: W("a"), 2: W("e"), 3: W("u")})
        st["t"] = (pt, {0: w(C + (" S" if kind == "scycle" else " s")), 4: W("a")})
        st["u"] = (pu, {0: w(E + " u"), 6: W("a")})
    return Rec(kind, ROOT, {k: (pw(v[0]) if isinstance(v[0], str) else v[0], v[1]) for k, v in st.items()})

def digraph(R):
    nodes = [(s, e) for s in R.states for e in (1, -1)]
    adj = {n: [] for n in nodes}
    for s, e in nodes:
        for x in range(N):
            for l, d in R.lsec(s, e, x):
                if R.is_state(l): adj[(s, e)].append((l, d))
    return nodes, adj

def sccs(nodes, adj):
    idx, low, on, stack, out, c = {}, {}, set(), [], [], [0]
    def dfs(v):
        idx[v] = low[v] = c[0]; c[0] += 1; stack.append(v); on.add(v)
        for u in adj[v]:
            if u not in idx: dfs(u); low[v] = min(low[v], low[u])
            elif u in on: low[v] = min(low[v], idx[u])
        if low[v] == idx[v]:
            comp = []
            while True:
                u = stack.pop(); on.discard(u); comp.append(u)
                if u == v: break
            out.append(comp)
    for v in nodes:
        if v not in idx: dfs(v)
    return out

def analyse(R, order2=False):
    if not R.unit_weight(): return ("notU",)
    nodes, adj = digraph(R)
    comps = sccs(nodes, adj)
    cyc_len, sccof = {}, {}
    for i, cp in enumerate(comps):
        for v in cp: sccof[v] = i
    for i, cp in enumerate(comps):
        inner = {v: [u for u in adj[v] if sccof[u] == i] for v in cp}
        if len(cp) == 1 and not inner[cp[0]]: continue
        if any(len(inner[v]) != 1 for v in cp): return ("exponential",)
        for v in cp: cyc_len[v] = len(cp)
    p = 1
    for L in cyc_len.values(): p = lcm(p, L)
    # degrees on the SCC DAG
    deg = {}
    def dg(v):
        if v in deg: return deg[v]
        below = [dg(u) for u in adj[v] if sccof[u] != sccof[v]]
        m = max(below, default=-1)
        if v in cyc_len:
            m = max(m, max((dg(u) for x in comps[sccof[v]] for u in adj[x] if sccof[u] != sccof[v]), default=-1))
            d = 1 + m
        else: d = m
        deg[v] = d; return d
    for v in nodes: dg(v)
    letdeg = {s: max(deg[(s, 1)], deg[(s, -1)]) for s in R.states}
    top = max(letdeg.values())
    if top <= 0: return ("bounded", p)
    # D: reachable after leaving a cycle
    D, todo = set(), [u for v in cyc_len for u in adj[v] if sccof[u] != sccof[v]]
    while todo:
        u = todo.pop()
        if u in D: continue
        D.add(u); todo.extend(adj[u])
    Dl = {s for s, _ in D}
    # level-p loops
    ls = R.loop_states(p)
    cnt = Counter((s, e) for s, e, *_ in ls)
    cycl = {s for s, _ in cyc_len}
    if any(cnt[(s, e)] != 1 for s in cycl for e in (1, -1)) or set(s for s, _ in cnt) != cycl:
        return ("L1p-fails", p)
    edges = R.loop_graph(p)
    pos = [ed for ed in edges if ed[3][1] == 1]
    par = {}
    def f(x):
        par.setdefault(x, x)
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for i, o, _, _ in pos: par[f(i)] = f(o)
    lam, lamg = {}, {}
    for i, o, lab, (s, e, y) in pos:
        lam.setdefault(f(i), []).append((s, lab)); lamg.setdefault(f(i), []).append((i, o, s))
    # (N)
    for _, _, lab, _ in pos:
        if R.trivial(lab): return ("loop-trivial", p)
    # (G') some commutator [x, s] (x in {a, e}, s a top-degree cycle letter) has a level-1
    # section c s'^(+-1) d with s' a top-degree cycle letter: G' is not inside Pol(top-1).
    topcyc = [s for s in cycl if letdeg[s] == top]
    gtop = False
    for x in ("a", "e"):
        for s in topcyc:
            g = W(x.upper() + " " + s.upper() + " " + x + " " + s)
            for y in range(N):
                u = R.sec(g, y)
                st = [l for l, _ in u if R.is_state(l)]
                if len(st) == 1 and st[0] in topcyc: gtop = True
    fails, edge_labs, how = [], [], Counter()
    for root, L in lam.items():
        letters = {s for s, _ in L}
        El = [(s, lab) for s, lab in L if s in Dl]
        # free split: the E-edges of Lam form a forest and rank(Lam) <= 1, so the leaf is
        # C_c (cyclic or trivial) with an empty edge to the centre.
        gr = lamg[root]; verts = {v for i, o, _ in gr for v in (i, o)}
        rank = len(gr) - len(verts) + 1
        q = {}
        def g(x):
            q.setdefault(x, x)
            while q[x] != x: q[x] = q[q[x]]; x = q[x]
            return x
        forest = True
        for i, o, s in gr:
            if s in Dl:
                if g(i) == g(o): forest = False
                else: q[g(i)] = g(o)
        if forest and rank <= 1:
            how["free-rank%d" % rank] += 1; continue
        if len(El) > 1:
            if gtop and all(letdeg[s] < top for s, _ in El): how["a2"] += 1
            else: fails.append(("a", tuple(sorted(s for s, _ in El))))
        else: how["a1"] += 1
        edge_labs += [lab for _, lab in El]
        if max(letdeg[s] for s in letters) == top:
            if group_order([R.perm(lab) for _, lab in L]) < 7920: how["b-root"] += 1
            else:
                k = intransitive_level(R, [lab for _, lab in L])
                if k: how["b-level%d" % k] += 1
                elif order2 and level2_order(R, [lab for _, lab in L]) < 7920 ** 12:
                    fails.append(("b-level2-proper", tuple(sorted(letters))))
                else: fails.append(("b", tuple(sorted(letters))) + (("level2-full",) if order2 else ()))
        else: how["b-lowdeg"] += 1
    if fails: return ("survivor", p, tuple(fails))
    infin = any(R.order(lab, bound=ORDB) is None for lab in edge_labs)
    return ("star", p, tuple(sorted(how)), infin)

def level2_order(R, gens):
    """order of the level-2 image of <gens> (G_2 = M_11 wr M_11 has order 7920^12)"""
    from sympy.combinatorics import Permutation, PermutationGroup
    pts = list(itertools.product(range(N), repeat=2)); ix = {y: i for i, y in enumerate(pts)}
    return PermutationGroup([Permutation([ix[R.act(g, y)] for y in pts]) for g in gens]).order()

def intransitive_level(R, gens, levels=(2, 3)):
    """least k in levels at which <gens> is intransitive on X^k (G is level-transitive), else 0"""
    for k in levels:
        pts = list(itertools.product(range(N), repeat=k))
        seen, todo = {pts[0]}, [pts[0]]
        while todo:
            y = todo.pop()
            for g in gens:
                z = R.act(g, y)
                if z not in seen: seen.add(z); todo.append(z)
        if len(seen) < len(pts): return k
    return 0

def main():
    global DECOS
    args = [a for a in sys.argv[1:] if a != "--full"]
    if "--full" in sys.argv: DECOS = DECOS_FULL
    kinds = args or ["chain", "fan", "cycle", "scycle"]
    for kind in kinds:
        tally, surv = Counter(), []
        for ps, pt, pu in itertools.product(PERMWORDS, repeat=3):
            for A, C, E in itertools.product(DECOS, repeat=3):
                R = family(kind, ps, pt, pu, A, C, E)
                v = analyse(R)
                key = v[0] if v[0] != "star" else ("star", v[1], v[2], "edge-without-finite-order<=%d" % ORDB if v[3] else "edge-orders-finite")
                if v[0] == "survivor":
                    key = ("survivor", v[1], tuple(sorted({c for c, _ in v[2]})))
                    if len(surv) < 12: surv.append((ps, pt, pu, A, C, E, analyse(R, order2=True)[2]))
                tally[key] += 1
        print("== family", kind, "total", sum(tally.values()))
        for k, n in sorted(tally.items(), key=str): print("  ", k, n)
        for x in surv: print("   survivor", x)
        sys.stdout.flush()

if __name__ == "__main__":
    main()
