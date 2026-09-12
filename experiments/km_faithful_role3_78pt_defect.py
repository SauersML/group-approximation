"""Faithful role-3 first-level defect on the 78-point arena
U_B2(2) u_{U_{-a3}} U_G2(2), over the envelope of consistent G2
unipotent presentations.

B2 block (16): (i,j,k,l) = a^i b^j c^k d^l, a = x_{-a1}, c = x_{-a3},
   b = x_{-a1-a3}, d = x_{-a1-2a3};  c^k a^i = a^i c^k (bd)^{ki}.
G2 block (64): exponent vectors in roots (x0..x5), x0 = x_{-a3}.
Glue: c <-> x0 (the shared U_{-alpha_3}).
H1 = <a> (B2 side), H2 = <x1> = U_{-a2} (G2 side), H3 = <c>=<x0> (both).
Adversary: full blocks.  Defect = dim[C_H3 cap (C_H1+C_H2)] - dim[V1+V2].
"""
import numpy as np, json
from itertools import product as iproduct
src = open('experiments/km_g2_unipotent_envelope.py').read()
ns = {}; exec(src.split('def group_ok')[0], ns)
build = ns['build']

def m_b2(x,y):
    i1,j1,k1,l1 = x; i2,j2,k2,l2 = y
    return ((i1+i2)%2,(j1+j2+k1*i2)%2,(k1+k2)%2,(l1+l2+k1*i2)%2)
B2 = [t for t in iproduct(range(2),repeat=4)]

def run(bits):
    els, idx64, T = build(bits)
    # arena points: ('B', t) for t in B2 with k-only part NOT pure <c>,
    # ('G', v) for v in els; identify c^k <-> x0^k
    def canonB(t):
        if t[0]==0 and t[1]==0 and t[3]==0: return ('D', t[2])
        return ('B', t)
    def canonG(v):
        if v[1:]==(0,0,0,0,0): return ('D', v[0])
        return ('G', v)
    U = []
    for t in B2:
        p = canonB(t)
        if p not in U: U.append(p)
    for v in els:
        p = canonG(v)
        if p not in U: U.append(p)
    idx = {p:i for i,p in enumerate(U)}
    assert len(U) == 78, len(U)
    def actB(h, p):
        t = p[1] if p[0]=='B' else ((0,0,p[1],0) if p[0]=='D' else None)
        if t is None: return None
        return canonB(m_b2(h,t))
    def actG(hv, p):
        v = p[1] if p[0]=='G' else (((p[1],0,0,0,0,0)) if p[0]=='D' else None)
        if v is None: return None
        # left mult in G2 group: index arithmetic
        e_i = els.index(hv); v_i = els.index(v)
        return canonG(els[T[e_i, v_i]])
    def actD(k, p):
        # shared c^k acts on everything
        if p[0]=='B' or (p[0]=='D'): 
            t = p[1] if p[0]=='B' else (0,0,p[1],0)
            return canonB(m_b2((0,0,k,0),t))
        return actG((k,0,0,0,0,0), p)
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
    H1 = orbspace([lambda p: actB((1,0,0,0),p)])
    H2 = orbspace([lambda p: actG((0,1,0,0,0,0),p)])
    H3 = orbspace([lambda p: actD(1,p)])
    V1 = orbspace([lambda p: actB((1,0,0,0),p), lambda p: actB((0,0,1,0),p)])
    V2 = orbspace([lambda p: actG((0,1,0,0,0,0),p), lambda p: actG((1,0,0,0,0,0),p)])
    AB = np.hstack([H1,H2])
    num = rank(H3)+rank(AB)-rank(np.hstack([H3,AB]))
    from numpy.linalg import svd
    Mj = np.hstack([H3,-AB]); u,s_,vt = svd(Mj)
    null = vt[(s_>1e-9).sum():].T
    W = H3 @ null[:H3.shape[1],:]
    den = np.hstack([V1,V2])
    interUW = rank(den)+rank(W)-rank(np.hstack([den,W]))
    return num, interUW, num-interUW

cands = [(0,0,0,0,0,0,1,1),(0,0,1,0,0,0,1,1),(1,1,0,0,1,1,1,1),(1,1,1,0,1,1,1,1)]
for bits in cands:
    n,d,df = run(bits)
    print(f"bits={bits}: numerator={n} denom-in-num={d} DEFECT={df}")
