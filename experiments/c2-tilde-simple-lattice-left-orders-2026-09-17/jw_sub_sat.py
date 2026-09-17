# Positive-cone SAT for the normal subgroups N_j (j=1,2,3) of K = pi_1(S_JW) with K/N_j = Z/2^j.
# K^ab = Z x Z/3 (GAP, jw_2power.out), so each N_j is the unique normal subgroup of K with a 2-group
# quotient of order 2^j.  Membership: Gamma_JW acts on the right on the cosets of N_j (FactorCosetAction,
# point 1 = the coset N_j, checked in GAP); a normal-form word w lies in N_j iff 1^w = 1.
# Calibration 'prod': reducible JW letters (all squares commute, group F_2 x F_2) with the subgroup
# {even/even, horizontal exponent sum = 0 mod 2^j}, which is a subgroup of F_2 x F_2, hence left-orderable.
import sys, json, time
from pysat.solvers import Cadical153, Glucose4
import bmw_sat
PERMS=json.load(open('jw_2power.json'))
def run(name,j,L):
    t=time.time()
    bmw_sat.selftest(name,300)
    H,V,I,SQ,mul,word,inv=bmw_sat.make(name)
    if name=='jw':
        P=PERMS[str(j)]; idx={'a':0,'b':1,'x':2,'y':3}; n=len(P[0])
        perm={}
        for c,k in idx.items():
            p=[q-1 for q in P[k]]; ip=[0]*n
            for s,q in enumerate(p): ip[q]=s
            perm[c]=p; perm[I[c]]=ip
        # sanity: relators act trivially
        for r in bmw_sat.GROUPS['jw']['rel']:
            for s in range(n):
                q=s
                for c in r: q=perm[c][q]
                assert q==s
        def member(g):
            q=0
            for c in g[0]+g[1]: q=perm[c][q]
            return q==0
    else:
        def member(g):
            v,h=g; e=sum(1 if c in 'ab' else -1 for c in h)
            return len(v)%2==0 and len(h)%2==0 and e%(2**j)==0
    gens=[((c,),()) for c in V]+[((),(c,)) for c in H]
    e=((),()); ball={e:0}; els=[e]; layer=[e]
    for d in range(L):
        nl=[]
        for g in layer:
            for s in gens:
                m=mul(g,s)
                if m not in ball: ball[m]=len(els); els.append(m); nl.append(m)
        layer=nl
    Nel=[i for i in range(1,len(els)) if member(els[i])]
    # consistency: membership is a subgroup property on the ball
    cls=[]
    for i in Nel:
        jj=ball[inv(els[i])]; assert member(els[jj]) and jj!=i
        if i<jj: cls+=[[i,jj],[-i,-jj]]
    for i in Nel:
        gi=els[i]
        for k in Nel:
            m=ball.get(mul(gi,els[k]))
            if m is None: continue
            assert member(els[m])
            cls.append([-i,-k] if m==0 else [-i,-k,m])
    res=[]
    for S in (Cadical153,Glucose4):
        with S(bootstrap_with=cls) as s: res.append(s.solve())
    assert res[0]==res[1]
    return dict(group=name,j=j,index_in_K=2**j,radius=L,ball=len(els),N_elements=len(Nel),clauses=len(cls),sat=res[0],secs=round(time.time()-t,1))
if __name__=="__main__":
    name=sys.argv[1]; j=int(sys.argv[2])
    for L in map(int,sys.argv[3:]): print(run(name,j,L),flush=True)
