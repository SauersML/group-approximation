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

# Refined defect: also quotient by the next-level gauge subspace
# C^Gnext with Gnext = <M3, [M1,M3], [M2,M3]> (unipotent shadow of the
# next B-chain level).
def comm(X,Y): 
    import numpy.linalg as la
    Xi = np.round(la.inv(X)).astype(np.int8)%2; Yi = np.round(la.inv(Y)).astype(np.int8)%2
    return (Xi@Yi@X@Y)%2

def refined(n, e1, e2, e3, label):
    M1,M2,M3 = mat(n,e1),mat(n,e2),mat(n,e3)
    if not np.array_equal((M1@M2)%2,(M2@M1)%2): print(f"{label}: skip"); return
    G = close([M1,M2,M3]); idx = {g.tobytes(): i for i,g in enumerate(G)}
    E = np.eye(n,dtype=np.int8)
    CA,CB,CC = (orbit_space(G,idx,[E,X]) for X in (M1,M2,M3))
    AC, BC = close([M1,M3]), close([M2,M3])
    CAC,CBC = orbit_space(G,idx,AC), orbit_space(G,idx,BC)
    Gnext = close([M3, comm(M1,M3), comm(M2,M3)])
    CGN = orbit_space(G,idx,Gnext)
    AB = np.hstack([CA,CB]); dCC,dAB = rank(CC),rank(AB)
    inter = dCC + dAB - rank(np.hstack([CC,AB]))
    den0 = rank(np.hstack([CAC,CBC]))
    denR_all = np.hstack([CAC,CBC,CGN])
    # refined denominator: (C13+C23+CGnext) cap (C3 cap (C1+C2))
    dDen, dNum = rank(denR_all), inter
    # dim of intersection of denR span with the numerator space:
    # numerator = CC cap span(AB); compute via joint kernel trick:
    # dim(U cap W) = dim U + dim W - dim(U+W) with U=span(denR), W=numerator.
    # numerator basis: get via nullspace pairing - approximate: numerator
    # dim known; U+W <= span(CC, AB-part...) - use: W <= CC, so
    # U cap W = (U cap CC) cap (U cap span AB)-superset... compute directly:
    # basis of W: solve CC x = AB y; use SVD-based nullspace of [CC | -AB].
    Mjoint = np.hstack([CC, -AB])
    from numpy.linalg import svd
    u,s,vt = svd(Mjoint); null = vt[(s>1e-8).sum():].T
    Wbasis = CC @ null[:CC.shape[1],:]  # columns span numerator W
    dW = rank(Wbasis); assert dW == inter, (dW, inter)
    dU = rank(denR_all)
    dUW = rank(np.hstack([denR_all, Wbasis]))
    interUW = dU + dW - dUW
    print(f"{label}: |G|={len(G)} |Gnext|={len(Gnext)} defect={inter-den0} "
          f"REFINED defect = {dW - interUW}")

refined(4, [(0,1)], [(2,3)], [(1,2)], "UT4 commuting-ends")
refined(5, [(0,1)], [(3,4)], [(1,2),(2,3)], "UT5 spread")
refined(5, [(0,1),(2,3)], [(0,2),(1,3)], [(3,4)], "UT5 mixed")
refined(6, [(0,1)], [(4,5)], [(1,2),(3,4)], "UT6 wide")

# Faithful arena shape: U = (AC-orbit of e) u (BC-orbit of e), two
# overlapping blocks glued along <C>-ish; functions supported on U.
# Numerator: h H3-inv on U, h = f1 + f2, f1 H1-inv supported on U1,
# f2 H2-inv supported on U2.  Denominator: (M13-inv on U1) + (M23-inv
# on U2) intersected with numerator.
def two_block(n, e1, e2, e3, label):
    M1,M2,M3 = mat(n,e1),mat(n,e2),mat(n,e3)
    if not np.array_equal((M1@M2)%2,(M2@M1)%2): print(f"{label}: skip"); return
    AC, BC = close([M1,M3]), close([M2,M3])
    U1 = {g.tobytes(): g for g in AC}; U2 = {g.tobytes(): g for g in BC}
    U = list({**U1, **U2}.values()); idx = {g.tobytes(): i for i,g in enumerate(U)}
    NU = len(U)
    def orbspace(sub, dom):
        # left-mult orbits of <sub> intersected with domain-support
        seen=set(); cols=[]
        for g in dom:
            k=g.tobytes()
            if k in seen: continue
            orb=set()
            for x in sub: 
                p=((x@g)%2).tobytes()
                orb.add(p)
            # orbit must stay inside U for a supported invariant function
            if not all(o in idx for o in orb): 
                seen|= {o for o in orb if o in idx}; continue
            seen|=orb
            v=np.zeros(NU)
            for o in orb: v[idx[o]]=1.0
            cols.append(v)
        return np.array(cols).T if cols else np.zeros((NU,0))
    E=np.eye(n,dtype=np.int8)
    C1 = orbspace([E,M1], AC)     # H1-inv, support in U1
    C2 = orbspace([E,M2], BC)     # H2-inv, support in U2
    C3 = orbspace([E,M3], U)      # H3-inv on U (orbits inside U)
    C13 = orbspace(AC, AC); C23 = orbspace(BC, BC)
    AB = np.hstack([C1,C2])
    dC3,dAB = rank(C3),rank(AB)
    inter = dC3 + dAB - rank(np.hstack([C3,AB]))
    from numpy.linalg import svd
    Mj = np.hstack([C3,-AB]); u,s,vt = svd(Mj) if Mj.size else (None,np.array([]),None)
    null = vt[(s>1e-8).sum():].T
    W = C3 @ null[:C3.shape[1],:] if C3.size else np.zeros((NU,0))
    den = np.hstack([C13,C23])
    dU_,dW_ = rank(den), rank(W)
    interUW = dU_ + dW_ - rank(np.hstack([den,W]))
    print(f"{label}: |U|={NU} (|U1|={len(AC)},|U2|={len(BC)}) "
          f"num={inter} den-in-num={interUW} TWO-BLOCK DEFECT={inter-interUW}")

two_block(4, [(0,1)], [(2,3)], [(1,2)], "UT4 commuting-ends")
two_block(5, [(0,1)], [(3,4)], [(1,2),(2,3)], "UT5 spread")
two_block(5, [(0,1),(2,3)], [(0,2),(1,3)], [(3,4)], "UT5 mixed")
two_block(6, [(0,1)], [(4,5)], [(1,2),(3,4)], "UT6 wide")
