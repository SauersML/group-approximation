"""Probe: finite-level three-subspace defect for nilpotent triples.

Model: G = <M1,M2,M3> unitriangular over F2 with [M1,M2]=1 (the
m_12=2 digon constraint of the (2,4,6) triple).  Subgroups A,B,C of
order 2 (q=2 root groups).  Function space R^G with orbit-constancy
subspaces C_X (X acting by left mult; orbits = right cosets Xg).
Defect := dim( C_C cap (C_A + C_B) ) - dim( C_<A,C> + C_<B,C> ).
Nonzero defect = non-distributive triple = the finite-level shadow of
the H^2(Lambda, L^0) mechanism.
"""
import numpy as np, itertools

def mat(n, entries):
    M = np.eye(n, dtype=np.int8)
    for (i,j) in entries: M[i,j] = 1
    return M % 2

def close(gens, cap=5000):
    n = gens[0].shape[0]
    seen = {}; frontier = [np.eye(n, dtype=np.int8)]
    seen[frontier[0].tobytes()] = frontier[0]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                p = (g @ h) % 2; k = p.tobytes()
                if k not in seen:
                    seen[k] = p; nxt.append(p)
                    if len(seen) > cap: raise RuntimeError("too big")
        frontier = nxt
    return list(seen.values())

def orbit_space(G, idx, sub):
    """columns: indicator of right cosets Xg -> basis of C_X."""
    n = len(G); seen = set(); cols = []
    for g in G:
        k = g.tobytes()
        if k in seen: continue
        orb = set()
        for x in sub: orb.add(((x @ g) % 2).tobytes())
        seen |= orb
        v = np.zeros(n); 
        for o in orb: v[idx[o]] = 1.0
        cols.append(v)
    return np.array(cols).T

def rank(M): return np.linalg.matrix_rank(M, tol=1e-8) if M.size else 0

def defect(n, e1, e2, e3, label):
    M1, M2, M3 = mat(n,e1), mat(n,e2), mat(n,e3)
    if not np.array_equal((M1@M2)%2, (M2@M1)%2):
        print(f"{label}: [M1,M2] != 1, skip"); return
    G = close([M1,M2,M3]); N = len(G)
    idx = {g.tobytes(): i for i,g in enumerate(G)}
    A,Bs,C = [np.eye(n,dtype=np.int8),M1],[np.eye(n,dtype=np.int8),M2],[np.eye(n,dtype=np.int8),M3]
    CA, CB, CC = (orbit_space(G,idx,S) for S in (A,Bs,C))
    AC = close([M1,M3]); BC = close([M2,M3])
    CAC, CBC = orbit_space(G,idx,AC), orbit_space(G,idx,BC)
    # C_C cap (C_A + C_B): kernel pairing
    AB = np.hstack([CA, CB])
    # intersection dim = dim CC + dim span(AB) - dim(CC + AB)
    dCC, dAB = rank(CC), rank(AB)
    dSum = rank(np.hstack([CC, AB]))
    inter = dCC + dAB - dSum
    denom = rank(np.hstack([CAC, CBC]))
    # denominator subspace is inside the intersection (check dims consistent)
    print(f"{label}: |G|={N} |AC|={len(AC)} |BC|={len(BC)} "
          f"dim(C3 cap (C1+C2))={inter} dim(C13+C23)={denom} DEFECT={inter-denom}")

# Model 1: UT(4,2)-style, generic positions
defect(4, [(0,1)], [(1,2)], [(2,3)], "UT4 chain")
# but [M1,M2] != 1 there; commuting pair variants:
defect(4, [(0,1)], [(2,3)], [(1,2)], "UT4 commuting-ends")
defect(5, [(0,1)], [(3,4)], [(1,2),(2,3)], "UT5 spread")
defect(5, [(0,1),(2,3)], [(0,2),(1,3)], [(3,4)], "UT5 mixed")
defect(6, [(0,1)], [(4,5)], [(1,2),(3,4)], "UT6 wide")
defect(6, [(0,1),(3,4)], [(1,2),(4,5)], [(2,3)], "UT6 interleave"
       )
