#!/usr/bin/env python3
"""Linear descent certificate: exponent-sum functionals that descend to G.

For a unit-weight polynomial recursion with state letters S, E(w) in Z^S is the vector of
signed state-letter exponent sums, and sum_x E(w|_x) = M E(w).  Put N = M^p - I (nilpotent).
For each section-closed letter set D (smallest first) we build Lam_D, a space of functionals
lam (supported on D) that vanish on E(trivial words of F(D) * P).  One round adds every lam with
  (i)  lam N in span(Lam_D) on the D-columns (lam E is conserved p levels down, on relators)
  (ii) lam(K_D) = 0, where K_D = { r in C_D : Lam_D(r) = 0, N r = 0 },
  (iii) lam agrees on the D_low-columns with an element of span(Lam_{D_low}).
C_D is the E-image of the cycle space of the level-p loop graph restricted to the D-edges,
and D_low is the section closure of the letters reached from D through a section leaving the
letter's strongly connected component.  See the proof file for why (i)-(iii) suffice.
Output: (p, dim Lam_S, Lam_S).  b_1(G) >= dim Lam_S; if it is >= 1, G is not of type FP_2
(fully-self-replicating-fp2-groups-have-odd-cyclic-h1, item 3), so not finitely presented.
"""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
import sys, itertools
from sympy import Matrix, zeros, eye
from poly_star_screen import family, digraph, sccs
from loopgraph import N as NX

def span(vecs, n):
    vecs = [v for v in vecs if any(v)]
    if not vecs: return []
    Mx = Matrix(vecs).rref()[0]
    return [list(Mx.row(i)) for i in range(Mx.rows) if any(Mx.row(i))]

def nullvecs(rows, n):  # vectors r with row.r = 0 for all rows (as lists)
    if not rows: return [list(eye(n).row(i)) for i in range(n)]
    ns = Matrix(rows).nullspace()
    return [list(v.T) for v in ns]

def certify(R, verbose=False):
    S = sorted(R.states); k = len(S); ix = {s: i for i, s in enumerate(S)}
    Mt = zeros(k, k)
    for s in S:
        for x in range(NX):
            for l, e in R.lsec(s, 1, x):
                if l in ix: Mt[ix[l], ix[s]] += e
    nodes, adj = digraph(R); comps = sccs(nodes, adj)
    scc = {}
    for i, c in enumerate(comps):
        for v in c: scc[v] = i
    lens = [len(c) for c in comps if len(c) > 1 or c[0] in adj[c[0]]]
    from math import lcm
    p = 1
    for L in lens: p = lcm(p, L)
    # sign period: M^p restricted to each cycle must be the identity -> make p work
    Np = None
    for q in range(1, 9):
        cand = Mt ** (p * q) - eye(k)
        if (cand ** k).is_zero_matrix: p = p * q; Np = cand; break
    assert Np is not None, "M^p not unipotent"
    assert R.unit_weight(), "(U) fails"
    # (T_p): for each s, at most one y in X^p has s|_y containing a letter of the signed SCC
    # of (s,1), and then that letter is s itself with exponent +1
    for s in S:
        fr = [((s, 1),)]
        for _ in range(p): fr = [R.sec(w, x) for w in fr for x in range(NX) if R.weight(R.sec(w, x)) == 1]
        hits = []
        for w in fr:
            l = [q for q in w if R.is_state(q[0])][0]
            if scc[l] == scc[(s, 1)]: hits.append(l)
        assert len(hits) <= 1 and all(h == (s, 1) for h in hits), ("T_p fails", s, hits)
    # letters reached from s through a section that leaves the SCC of s
    exitl = {s: set() for s in S}
    for (s, e) in nodes:
        for (l, d) in adj[(s, e)]:
            if scc[(l, d)] != scc[(s, e)]: exitl[s].add(l)
    def closure(T):
        T = set(T); todo = list(T)
        while todo:
            s = todo.pop()
            for (l, d) in adj[(s, 1)] + adj[(s, -1)]:
                if l not in T: T.add(l); todo.append(l)
        return frozenset(T)
    Ds = sorted({closure([s]) for s in S} | {closure(T) for r in range(1, k + 1) for T in itertools.combinations(S, r)}, key=len)
    edges = [ed for ed in R.loop_graph(p) if ed[3][1] == 1]
    Lam = {frozenset(): []}
    for D in Ds:
        low = closure(set().union(*[exitl[s] for s in D])) if D else frozenset()
        assert low < D or not D
        ED = [(i, o, s) for i, o, _, (s, _, _) in edges if s in D]
        # cycle space image
        pot, C = {}, []
        adjg = {}
        for i, o, s in ED:
            adjg.setdefault(i, []).append((o, s, 1)); adjg.setdefault(o, []).append((i, s, -1))
        used = set()
        for v0 in adjg:
            if v0 in pot: continue
            pot[v0] = [0] * k; st = [v0]
            while st:
                v = st.pop()
                for w, s, sg in adjg[v]:
                    if w not in pot:
                        pot[w] = [a + (sg if j == ix[s] else 0) for j, a in enumerate(pot[v])]; st.append(w)
        for i, o, s in ED:
            C.append([pot[i][j] + (1 if j == ix[s] else 0) - pot[o][j] for j in range(k)])
        Cb = span(C, k)
        # (iii) lam restricted to D_low lies in span(Lam_low) restricted to D_low
        lowb = Lam[low]
        L = []
        while True:
            # K' = C_D cap ker(L) cap ker(N)
            if Cb:
                B = Matrix(Cb).T  # columns span C_D
                cons = [list(Matrix([row]) * B) for row in L] + [list(Np.row(j) * B) for j in range(k)]
                coef = nullvecs(cons, B.cols)
                K = [list(B * Matrix(c)) for c in coef]
            else: K = []
            # unknowns: lam (k), c (len L), b (len lowb):  lam N = c L on D-columns,
            # lam = b Lam_low on D_low-columns, lam = 0 off D, lam(K) = 0
            nl, nb = len(L), len(lowb); rows = []
            z = [0] * (nl + nb)
            for kv in K: rows.append([kv[j] for j in range(k)] + z)
            for j in range(k):
                if S[j] not in D: rows.append([1 if jj == j else 0 for jj in range(k)] + z)
            for col in range(k):
                if S[col] not in D: continue
                rows.append([Np[j, col] for j in range(k)] + [-L[a][col] for a in range(nl)] + [0] * nb)
                if S[col] in low:
                    rows.append([1 if jj == col else 0 for jj in range(k)] + [0] * nl + [-lowb[a][col] for a in range(nb)])
            sol = nullvecs(rows, k + nl + nb)
            new = span([v[:k] for v in sol], k)
            if len(new) <= len(L): break
            L = new
        Lam[D] = L
        if verbose: print("  D", sorted(D), "low", sorted(low), "C_D", Cb, "Lam", L)
    return p, len(Lam[frozenset(S)]), Lam[frozenset(S)]

if __name__ == "__main__":
    args = sys.argv[1:] or ["chain", "a", "a", "e", "", "", ""]
    args = [a if a != "-" else "" for a in args]
    print(certify(family(*args), verbose=True))
