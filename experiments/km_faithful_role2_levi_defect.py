"""Faithful role-2 defect at the LEVI level (radical depth 0).

G2 = L_13 = Sp4(2) as 4x4 F2 matrices, basis (e1,e2,f2,f1),
     L1 = long-root SL2 acting in (e2,f2): <I+E12, I+E21>,
     L3 = short-root SL2: <I+E01+E23, I+E10+E32>.
G1 = L_12 = L1 x S3 (second factor = L2, interacting with nothing).
Glue along D = L1 (order 6).  Arena |U| = 36 + 720 - 6 = 750.
H1 = L1 (both blocks), H2 = second factor of G1, H3 = L3 in G2.
Adversary: full G1, G2.
"""
import numpy as np
from itertools import permutations

def M(*entries):
    m = np.eye(4, dtype=np.int8)
    for (i,j) in entries: m[i,j] ^= 1
    return m
x_l, x_ml = M((1,2)), M((2,1))            # long +-
x_s, x_ms = M((0,1),(2,3)), M((1,0),(3,2)) # short +-
def close(gens):
    seen = {}
    frontier = [np.eye(4,dtype=np.int8)]
    seen[frontier[0].tobytes()] = frontier[0]
    while frontier:
        nxt=[]
        for g in frontier:
            for h in gens:
                p=(g@h)%2; k=p.tobytes()
                if k not in seen: seen[k]=p; nxt.append(p)
        frontier=nxt
    return seen
L1 = close([x_l,x_ml]); L3 = close([x_s,x_ms])
SP = close([x_l,x_ml,x_s,x_ms])
assert (len(L1),len(L3),len(SP)) == (6,6,720), (len(L1),len(L3),len(SP))
S3 = list(permutations(range(3)))
def ms(a,b): return tuple(a[b[i]] for i in range(3))
ID3 = (0,1,2)
# arena points: ('L',(l1key,s)) with s != ID3, ('R', spkey), D-pts = ('R', l1key)
U = [('L',(k,s)) for k in L1 for s in S3 if s != ID3] + [('R',k) for k in SP]
idx = {p:i for i,p in enumerate(U)}
assert len(U) == 750, len(U)

def actG1(h1key, hs, p):
    """left-mult by (h1,hs) in G1; h1key bytes of L1 matrix, hs in S3."""
    t,g = p
    if t=='L':
        k,s = g; prod = ((L1[h1key] @ np.frombuffer(k,dtype=np.int8).reshape(4,4))%2)
        ns = ms(hs,s)
        return ('R', prod.tobytes()) if ns==ID3 else ('L',(prod.tobytes(),ns))
    else:
        # R-point: in G1 only if it's a D-point (matrix in L1)
        if g in L1:
            prod = ((L1[h1key] @ L1[g])%2)
            return ('R',prod.tobytes()) if hs==ID3 else ('L',(prod.tobytes(),hs))
        return None
def actG2(hkey_mat, p):
    t,g = p
    if t=='R':
        prod = ((hkey_mat @ np.frombuffer(g,dtype=np.int8).reshape(4,4))%2)
        return ('R', prod.tobytes())
    else:
        k,s = g
        if hkey_mat.tobytes() in L1:
            prod = ((hkey_mat @ np.frombuffer(k,dtype=np.int8).reshape(4,4))%2)
            return ('L',(prod.tobytes(),s))
        return None
def orbspace(movers):
    """movers: list of callables p -> p' or None."""
    seen=set(); cols=[]
    for p in U:
        if p in seen: continue
        orb={p}; frontier=[p]; ok=True
        while frontier:
            nxt=[]
            for q in frontier:
                for mv in movers:
                    r = mv(q)
                    if r is None: ok=False; continue
                    if r not in orb: orb.add(r); nxt.append(r)
            frontier=nxt
        seen|=orb
        if ok:
            v=np.zeros(len(U))
            for o in orb: v[idx[o]]=1.0
            cols.append(v)
    return np.array(cols).T if cols else np.zeros((len(U),0))
rank = lambda A: np.linalg.matrix_rank(A,tol=1e-9) if A.size else 0
def actD(mat, p):
    "a D-element (mat in L1) acts on EVERYTHING as a lattice element"
    t,g = p
    if t=='L':
        k,s = g
        prod = ((mat @ np.frombuffer(k,dtype=np.int8).reshape(4,4))%2)
        return ('L',(prod.tobytes(),s))
    prod = ((mat @ np.frombuffer(g,dtype=np.int8).reshape(4,4))%2)
    return ('R', prod.tobytes())
l1gens = [x_l.tobytes(), x_ml.tobytes()]
H1 = orbspace([lambda p,m=m: actD(m,p) for m in (x_l,x_ml)])
H2 = orbspace([lambda p,s=s: actG1(np.eye(4,dtype=np.int8).tobytes(),s,p)
               for s in [(1,0,2),(1,2,0)]])
H3 = orbspace([lambda p,m=m: actG2(m,p) for m in (x_s,x_ms)])
V1 = orbspace([lambda p,m=m: actD(m,p) for m in (x_l,x_ml)] +
              [lambda p,s=s: actG1(np.eye(4,dtype=np.int8).tobytes(),s,p)
               for s in [(1,0,2),(1,2,0)]])
V2 = orbspace([lambda p,m=m: actG2(m,p) for m in (x_l,x_ml,x_s,x_ms)])
AB = np.hstack([H2,H3])
num = rank(H1)+rank(AB)-rank(np.hstack([H1,AB]))
from numpy.linalg import svd
Mj = np.hstack([H1,-AB]); u,s_,vt = svd(Mj)
null = vt[(s_>1e-9).sum():].T
W = H1 @ null[:H1.shape[1],:]
den = np.hstack([V1,V2])
inter = rank(den)+rank(W)-rank(np.hstack([den,W]))
print(f"|U|={len(U)} dims: H1={rank(H1)} H2={rank(H2)} H3={rank(H3)} "
      f"V1={rank(V1)} V2={rank(V2)}")
print(f"numerator dim(C_H1 cap (C_H2+C_H3)) = {num}")
print(f"denominator-in-numerator = {inter}")
print(f"FAITHFUL LEVI-LEVEL ROLE-2 DEFECT = {num-inter}")
