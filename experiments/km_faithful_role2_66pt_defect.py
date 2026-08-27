"""Role-2 faithful first-level defect: U_{A1xA1}(2) u_{U_{-a2}} U_G2(2),
66 points, over the consistent G2-presentation envelope.
Shared subgroup: u2 (A1xA1 second factor) <-> x1 = x_{-alpha_2}.
H2 = shared <u2>=<x1>; H1 = <u1> (block 1); H3 = <x0> = U_{-a3} (block 2).
Numerator: C_H2 cap (C_H1 + C_H3); denominator: C_V1 + C_V2 (full blocks).
"""
import numpy as np
from itertools import product as iproduct
src = open('experiments/km_g2_unipotent_envelope.py').read()
ns = {}; exec(src.split('def group_ok')[0], ns)
build = ns['build']

A22 = [(i,j) for i in range(2) for j in range(2)]  # u1^i u2^j
def m_a(x,y): return ((x[0]+y[0])%2,(x[1]+y[1])%2)

def run(bits):
    els, idx64, T = build(bits)
    def canonA(t):
        if t[0]==0: return ('D', t[1])       # u2^j ~ x1^j
        return ('A', t)
    def canonG(v):
        if v[0]==0 and v[2:]==(0,0,0,0): return ('D', v[1])
        return ('G', v)
    U = []
    for t in A22:
        p = canonA(t)
        if p not in U: U.append(p)
    for v in els:
        p = canonG(v)
        if p not in U: U.append(p)
    idx = {p:i for i,p in enumerate(U)}
    assert len(U) == 66, len(U)
    def actA(h, p):
        t = p[1] if p[0]=='A' else ((0,p[1]) if p[0]=='D' else None)
        if t is None: return None
        return canonA(m_a(h,t))
    def actG(hv, p):
        v = p[1] if p[0]=='G' else ((0,p[1],0,0,0,0) if p[0]=='D' else None)
        if v is None: return None
        return canonG(els[T[els.index(hv), els.index(v)]])
    def actD(j, p):
        if p[0] in ('A',): return canonA(m_a((0,j), p[1]))
        if p[0]=='D': return canonA(m_a((0,j),(0,p[1])))
        return actG((0,j,0,0,0,0), p)
    def orbspace(movers):
        seen=set(); cols=[]
        for p in U:
            if p in seen: continue
            orb={p}; fr=[p]; ok=True
            while fr:
                nx=[]
                for q in fr:
                    for mv in movers:
                        r = mv(q)
                        if r is None: ok=False; continue
                        if r not in orb: orb.add(r); nx.append(r)
                fr=nx
            seen|=orb
            if ok:
                v=np.zeros(len(U))
                for o in orb: v[idx[o]]=1.0
                cols.append(v)
        return np.array(cols).T if cols else np.zeros((len(U),0))
    rank = lambda A: np.linalg.matrix_rank(A,tol=1e-9) if A.size else 0
    H1 = orbspace([lambda p: actA((1,0),p)])
    H3 = orbspace([lambda p: actG((1,0,0,0,0,0),p)])
    H2 = orbspace([lambda p: actD(1,p)])
    V1 = orbspace([lambda p: actA((1,0),p), lambda p: actA((0,1),p)])
    V2 = orbspace([lambda p: actG((1,0,0,0,0,0),p), lambda p: actG((0,1,0,0,0,0),p)])
    AB = np.hstack([H1,H3])
    num = rank(H2)+rank(AB)-rank(np.hstack([H2,AB]))
    from numpy.linalg import svd
    Mj = np.hstack([H2,-AB]); u,s_,vt = svd(Mj)
    null = vt[(s_>1e-9).sum():].T
    W = H2 @ null[:H2.shape[1],:]
    den = np.hstack([V1,V2])
    interUW = rank(den)+rank(W)-rank(np.hstack([den,W]))
    return num, interUW, num-interUW

for bits in [(0,0,0,0,0,0,1,1),(0,0,1,0,0,0,1,1),(1,1,0,0,1,1,1,1),(1,1,1,0,1,1,1,1)]:
    n,d,df = run(bits)
    print(f"bits={bits}: numerator={n} den-in-num={d} DEFECT={df}")
