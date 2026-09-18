"""The three I2(5) flats V for which l_x stays modular in B_V = A_x u A_y u A_V (21 walls, 6 fibre points).
Prints the collision arrangement in the base (walls of A_x on which two fibre points meet), its
characteristic polynomial coefficients (Whitney numbers, via the Moebius function of the flat lattice),
and its modular lines.  Result: 10 collision planes, chi(t) = t^3-10t^2+29t-20 = (t-1)(t-4)(t-5),
supersolvable (a modular line with 5 planes).  Run: python3 i25probe.py > i25probe.log."""
import itertools, numpy as np
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'h4-case1-fibred-quotient-2026-09-17'))
from fibred import setup, through, walls, is_wall
n,sim,W,om=setup('H4'); x=om[0]; y=om[3]
Ax=through(W,[x]); Ay=through(W,[y]); Az=through(W,[x,y])
Ap=walls(Ax+Ay); Ayz=[w for w in Ay if not is_wall(w,Az)]; Axz=[w for w in Ax if not is_wall(w,Az)]
def rank(vs): return np.linalg.matrix_rank(np.array(vs),tol=1e-8) if vs else 0
def charpoly(C):
    # Whitney: chi(t)=sum over subsets? use flats via closure: enumerate flats by rank
    m=len(C); flats={frozenset():0}; level=[frozenset()]
    mob={frozenset():1}
    allfl=[frozenset()]
    for r in range(1,5):
        new=set()
        for F in level:
            for i in range(m):
                if i in F: continue
                S=list(F)+[i]; rk=rank([C[j] for j in S])
                if rk!=r: continue
                cl=frozenset(j for j in range(m) if rank([C[k] for k in S]+[C[j]])==r)
                new.add(cl)
        level=list(new); allfl+=level
        for F in level: flats[F]=r
    for F in sorted(allfl,key=lambda F:flats[F]):
        if F: mob[F]=-sum(mob[G] for G in allfl if G<F)
    co={}
    for F in allfl: co[flats[F]]=co.get(flats[F],0)+mob[F]
    return co, flats
seen=set()
for w1 in Ayz:
  for w2 in Axz:
    B2=np.array([w1,w2]); P=B2.T@np.linalg.pinv(B2.T)
    AV=[w for w in W if np.linalg.norm(P@w-w)<1e-9]
    if len(AV)!=5: continue
    B=walls(Ap+AV); fib=[w for w in B if abs(np.dot(w,x))>1e-9]
    ok=True; coll=[]
    for u,v in itertools.combinations(fib,2):
        nv=np.dot(v,x)*u-np.dot(u,x)*v
        if not is_wall(nv,Ax): ok=False
        elif not is_wall(nv,coll): coll.append(nv/np.linalg.norm(nv))
    if not ok: continue
    base=coll; co,fl=charpoly(base)
    print('I2(5) fibred: fibre pts',len(fib),'rank fib',rank(fib),'collision walls',len(base),'base char coeffs',co)
    # modular lines of base: rank-2 flats X such that every pair of walls outside X meets X? test fibre-type
    lines=[F for F in fl if fl[F]==2]
    for L in lines:
        out=[i for i in range(len(base)) if i not in L]
        good=all(any(set(G)>={a,b} and len(set(G)&L)>0 for G in lines) for a,b in itertools.combinations(out,2))
        if good: print('   modular line with',len(L),'walls; fibre points',len(out))
