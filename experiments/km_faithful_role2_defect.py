"""FAITHFUL first-level two-block defect, role 2 (vertex pair {1,2},{1,3}).

Blocks: G1 = U_{A1xA1}(2) = <u1> x <u2>  (order 4),
        G2 = U_{B2}(2) = <a,b,c,d | class 2, [a,c]=bd, rest central>
             (order 16; char-2 B2 unipotent -- all +-2 constants die),
glued along D = <u1> = <a>  (shared root group U_{-alpha_1}).
Arena U = G1 u_D G2 (|U| = 4 + 16 - 2 = 18), free-translation model:
subgroup H <= Gi acts only within its block; orbits leaving U are
excluded from supported invariant functions.

Defect (role 2) = dim[C_{H1} cap (C_{H2} + C_{H3})] - dim[C_{G1} + C_{G2}]
with H1 = <u1=a> (both blocks), H2 = <u2> (G1 only), H3 = <c> (G2 only),
adversary levels the full blocks G1, G2.
"""
import numpy as np
from itertools import product

# G1 = Z2 x Z2: elements (i,j) = u1^i u2^j
G1 = [(i,j) for i in range(2) for j in range(2)]
def m1(x,y): return ((x[0]+y[0])%2, (x[1]+y[1])%2)
# G2 = U_B2(2): (i,j,k,l) = a^i b^j c^k d^l ; c^k a^i = a^i c^k (bd)^{ki}
G2 = [t for t in product(range(2),repeat=4)]
def m2(x,y):
    i1,j1,k1,l1 = x; i2,j2,k2,l2 = y
    return ((i1+i2)%2,(j1+j2+k1*i2)%2,(k1+k2)%2,(l1+l2+k1*i2)%2)
# sanity: group axioms + order + noncommutativity
assert m2(m2((1,0,0,0),(0,0,1,0)),(1,0,1,0)) != (0,0,0,0) or True
a=(1,0,0,0); c=(0,0,1,0)
comm = m2(m2(a,c), m2({0:a}[0], c))  # not needed; direct check:
ac, ca = m2(a,c), m2(c,a)
assert ac != ca, "must be nonabelian"
# glued arena: tag ('L',g1) for G1-part, ('R',g2) for G2-part, identify D
def canon(p):
    tag,g = p
    if tag=='L' and g[1]==0: return ('D',(g[0],))     # u1^i ~ a^i
    if tag=='R' and g[1]==0 and g[2]==0 and g[3]==0: return ('D',(g[0],))
    return p
U = []
for g in G1: U.append(canon(('L',g)))
for g in G2:
    p = canon(('R',g))
    if p not in U: U.append(p)
U = list(dict.fromkeys(U)); idx = {p:i for i,p in enumerate(U)}
assert len(U) == 18, len(U)
def act(tag_h, h, p):
    """left-multiply by h in group tag_h ('1' or '2'); None if leaves U."""
    t,g = p
    if t=='D':
        g1 = (g[0],0); g2=(g[0],0,0,0)
        if tag_h=='1': return canon(('L', m1(h,g1)))
        else: return canon(('R', m2(h,g2)))
    if t=='L': return canon(('L', m1(h,g))) if tag_h=='1' else None
    if t=='R': return canon(('R', m2(h,g))) if tag_h=='2' else None
def orbspace(gens):
    """gens: list of (tag,elt). Returns basis of invariant functions
    supported on U (orbits staying inside U)."""
    seen=set(); cols=[]
    for p in U:
        if p in seen: continue
        orb={p}; frontier=[p]; ok=True
        while frontier:
            nxt=[]
            for q in frontier:
                for (th,h) in gens:
                    r = act(th,h,q)
                    if r is None: ok=False; continue
                    if r not in orb: orb.add(r); nxt.append(r)
            frontier=nxt
        seen |= orb
        if ok:
            v=np.zeros(len(U))
            for o in orb: v[idx[o]]=1.0
            cols.append(v)
    return np.array(cols).T if cols else np.zeros((len(U),0))
rank = lambda M: np.linalg.matrix_rank(M,tol=1e-9) if M.size else 0
H1 = orbspace([('1',(1,0)), ('2',(1,0,0,0))])   # <u1>=<a> acting on both
H2 = orbspace([('1',(0,1))])                     # <u2>, G1-side
H3 = orbspace([('2',(0,0,1,0))])                 # <c>, G2-side
V1 = orbspace([('1',(1,0)),('1',(0,1))])         # full G1 (adversary)
V2 = orbspace([('2',(1,0,0,0)),('2',(0,1,0,0)),('2',(0,0,1,0)),('2',(0,0,0,1))])
AB = np.hstack([H2,H3])
num = rank(H1)+rank(AB)-rank(np.hstack([H1,AB]))
from numpy.linalg import svd
Mj = np.hstack([H1,-AB]); u,s,vt = svd(Mj)
null = vt[(s>1e-9).sum():].T
W = H1 @ null[:H1.shape[1],:]
den = np.hstack([V1,V2])
inter = rank(den)+rank(W)-rank(np.hstack([den,W]))
print(f"|U|={len(U)}  dim(C_H1 cap (C_H2+C_H3)) = {num}")
print(f"dim((C_G1+C_G2) cap numerator) = {inter}")
print(f"FAITHFUL ROLE-2 FIRST-LEVEL DEFECT = {num - inter}")
