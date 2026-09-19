# build Omega for the W(3) twisted level (A=B=opposition geometry, identity class matching)
# and compute reduced H_2(Omega; F2) simplicially; compare with coker dim = 24
exec(open('w3_opp.py').read().split('# --- rational surjectivity')[0])
import collections
# A-side data: vertices V (points, single-class) + Al (lines, all-class); edges = flags
Averts = [('A',x) for x in V]+[('A',x) for x in Al]
flagsA = [(('A',L),('A',p)) for L in Al for p in adj[L] if p in cls]
def clsof(side_v):
    tag,x = side_v
    return cls.get(x, None) if x[0]=='p' else None
# simplices of Omega: alpha*beta, alpha simplex of A (vertex or edge), beta of B; allowed unless
# I(alpha)=I(beta)={same single class}; I(edge/flag)= {class of its point}; I(point)={its class}; I(line)=all
def Iof(simplex):  # simplex: tuple of A-vertices (1 or 2 elements)
    ptcls=[cls[x] for (_,x) in simplex if x in cls]
    if len(simplex)==2:  # flag: line+point
        return frozenset(ptcls)  # {class of the point}
    (t,x),=simplex
    if x in cls: return frozenset([cls[x]])
    return None  # line vertex: all classes
def allowed(sa, sb):
    Ia, Ib = Iof(sa), Iof(sb)
    if Ia is None or Ib is None: return True
    return not (len(Ia)==1 and Ia==Ib)
# enumerate simplices of Omega up to dim 3
Vs_A = [(('A',x),) for x in V]+[(('A',x),) for x in Al]
Es_A = [tuple(sorted([('A',L),('A',p)])) for L in Al for p in adj[L] if p in cls]
Vs_B = [(('B',x),) for x in V]+[(('B',x),) for x in Al]
Es_B = [tuple(sorted([('B',L),('B',p)])) for L in Al for p in adj[L] if p in cls]
def relabel(s, side): return tuple((side,x) for (_,x) in s)
simp = {0:set(),1:set(),2:set(),3:set()}
for s in Vs_A: simp[0].add(s)
for s in Vs_B: simp[0].add(s)
for s in Es_A: simp[1].add(s)
for s in Es_B: simp[1].add(s)
for sa in Vs_A:
    for sb in Vs_B:
        if allowed(sa,sb): simp[1].add(tuple(sorted(sa+sb)))
for ea in Es_A:
    for sb in Vs_B:
        if allowed(ea,sb): simp[2].add(tuple(sorted(ea+sb)))
for sa in Vs_A:
    for eb in Es_B:
        if allowed(sa,eb): simp[2].add(tuple(sorted(sa+eb)))
for ea in Es_A:
    for eb in Es_B:
        if allowed(ea,eb): simp[3].add(tuple(sorted(ea+eb)))
S1=sorted(simp[1]); S2=sorted(simp[2]); S3=sorted(simp[3])
S0=sorted(simp[0])
print("counts:",len(S0),len(S1),len(S2),len(S3))
idx1={s:i for i,s in enumerate(S1)}; idx2={s:i for i,s in enumerate(S2)}
idx0={s:i for i,s in enumerate(S0)}
def faces(s):
    return [tuple(x for j,x in enumerate(s) if j!=i) for i in range(len(s))]
# NOTE: faces of a mixed simplex must themselves be simplices of Omega: check
def rank_f2(rows):
    piv={}; r=0
    for row in rows:
        while row:
            m=row.bit_length()-1
            if m in piv: row^=piv[m]
            else: piv[m]=row; r+=1; break
    return r
rows3=[]
for s in S3:
    v=0
    for f in faces(s):
        v ^= 1<<idx2[f]
    rows3.append(v)
r3=rank_f2(rows3)
print("rank d3 =",r3)
rows2=[]
for s in S2:
    v=0
    for f in faces(s):
        if f in idx1: v ^= 1<<idx1[f]
        else: raise RuntimeError("face missing "+str(f))
    rows2.append(v)
r2=rank_f2(rows2)
print("rank d2 =",r2)
b2 = (len(S2)-r2)-r3
print("H2(Omega;F2) dim =", b2, "(prediction 24)")
