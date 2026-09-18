# Normal-form word problem in the abstract amalgams A and verification that
# (1) every exact relation of K(nm) of length <= 12 (from A12_nm.g) is trivial in A,
# (2) the defining relations of A hold in K exactly (AG.trivial), and
# (3) rho: A -> S3 is a homomorphism with rho(G1) <= Stab(0) and rho(missing letter) moving 0.
# A(332V) = V4 * C2,  V4=<a0,a1>, a2=a0a1.
# A(332H), A(193V), A(193H) = C2^3 *_{<c>} S3, c = product of the three D-letters, S3=<tau,c>.
import re, sys
from aut import AUT
from agrp import AG
CFG = {  # D letters, tau letter, amalgamated (True: C2^3 *_c S3; False: V4*C2 with a2=a0a1)
 '332V': ((0,1,2),3,False), '332H': ((0,1,2),3,True),
 '193V': ((0,1,2),3,True),  '193H': ((0,1,3),2,True)}
def comp(p,q): return tuple(p[q[i]] for i in range(3))   # p after q
ID=(0,1,2); TAU=(1,0,2); CS=(0,2,1)                        # tau=(01), c=(12) in S3; tau*c of order 3
class Amal:
    def __init__(s,nm):
        s.D,s.t,s.am=CFG[nm]
        if s.am: s.dv={s.D[0]:(1,0,0),s.D[1]:(0,1,0),s.D[2]:(0,0,1)}; s.C=(1,1,1)
        else:    s.dv={s.D[0]:(1,0),s.D[1]:(0,1),s.D[2]:(1,1)}; s.C=None
    def zero(s,f): return (0,)*len(next(iter(s.dv.values()))) if f=='D' else ID
    def mul(s,f,x,y): return tuple(a^b for a,b in zip(x,y)) if f=='D' else comp(x,y)
    def inC(s,f,x):
        if s.C is None: return x==s.zero(f)
        return x in (s.zero('D'),s.C) if f=='D' else x in (ID,CS)
    def phi(s,f,x):  # C-element of factor f -> same element in the other factor
        if f=='D': return ID if x==s.zero('D') else CS
        return s.zero('D') if x==ID else s.C
    def trivial(s,w):
        st=[]
        for g in w:
            f,x=('D',s.dv[g]) if g in s.dv else ('S',TAU)
            if st and st[-1][0]==f:
                y=s.mul(f,st[-1][1],x); st.pop()
                if y==s.zero(f): continue
                if s.inC(f,y) and st:
                    h,z=st.pop(); st.append((h,s.mul(h,z,s.phi(f,y))))
                    continue
                st.append((f,y))
            else:
                if st and s.inC(*st[-1]):           # only possible at the bottom
                    h,z=st.pop(); x=s.mul(f,s.phi(h,z),x)
                    if x==s.zero(f): continue
                st.append((f,x))
        return all(x==s.zero(f) for f,x in st) and len(st)<=1
    def rho(s,g):   # a hom A->S3 killing the complement of <c> in D; D[1] -> c
        if g==s.t: return TAU
        if s.am: return CS if g==s.D[1] else ID
        return CS if g in (s.D[0],s.D[2]) else ID          # V4*C2: a0,a2 -> (12), a1 -> 1
def parse(fn):
    txt=open(fn).read()
    R=txt[txt.index('R:=[')+4:txt.index('];;\nA:=')]
    G=txt[txt.index('G1w:=[')+6:]; G=G[:G.index('];;')]
    toks=lambda e: tuple(int(t) for t in re.findall(r'x(\d)',e))
    rels=[toks(e) for e in R.split(',') if '^2' not in e]
    g1=[toks(e) for e in G.split(',')]
    return rels,g1
if __name__=='__main__':
    for nm in CFG:
        A=Amal(nm); rels,g1=parse('A12_%s.g'%nm)
        bad=[r for r in rels if not A.trivial(r)]
        out,sec=AUT[nm]; K=AG([out[g] for g in range(4)],[sec[g] for g in range(4)])
        D=A.D; t=A.t
        defs=[(g,g) for g in range(4)]+[(D[i],D[j],D[i],D[j]) for i in range(3) for j in range(i+1,3)]
        defs+= [(D[0],D[1],D[2],t)*3] if A.am else [(D[0],D[1],D[2])]
        okK=all(K.trivial(r)==True for r in defs)
        def rw(w):
            p=ID
            for g in w: p=comp(p,A.rho(g))
            return p
        okrho=all(rw(r)==ID for r in defs)
        pts=[p for p in range(3) if all(rw(w)[p]==p for w in g1)]; p0=pts[0] if pts else None; stab=pts
        miss=[g for g in range(4) if (g,) not in g1]
        print(nm,'K-rels(len<=12):',len(rels),'not trivial in A:',len(bad),
              '| A-defs hold in K:',okK,'| rho hom on A:',okrho,
              '| points fixed by rho(G1):',stab,'| missing letters',miss,'moved:',[rw((g,))[p0]!=p0 for g in miss])
        # sanity: normal form detects nontrivial elements
        assert not A.trivial((t,D[1])) and not A.trivial((t,D[0],t,D[1])) and not A.trivial((t,D[0])*5)
def relsec(nm):
    """sections of the defining relators of A are trivial in A (wreath recursion descends to A);
    left-first convention as in achain.g (reversal-closed relator set, so either convention works)."""
    A=Amal(nm); out,sec=AUT[nm]; D=A.D; t=A.t
    defs=[(D[i],D[j],D[i],D[j]) for i in range(3) for j in range(i+1,3)]
    defs+= [(D[0],D[1],D[2],t)*3] if A.am else [(D[0],D[1],D[2])]
    ok=True
    for r in defs:
        for rr in (r,tuple(reversed(r))):
            for x in range(3):
                y=x; w=[]
                for l in rr: w.append(sec[l][y]); y=out[l][y]
                ok &= (y==x) and A.trivial(w)
    return defs,ok
