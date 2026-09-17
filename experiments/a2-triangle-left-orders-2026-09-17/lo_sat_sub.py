# Positive-cone SAT for a finite-index subgroup H = Stab(point 1) of a coset action of Gamma_T.
# Only elements of H in the ball B_L get variables; products are taken inside B_L.
import json, sys, time
from kb import RWS, inv
from lo_sat import check_confluent, ball
from pysat.solvers import Cadical153, Glucose4
def run_sub(n,relators,perms,L):
    R=RWS(n,relators).complete(10,verbose=False); assert check_confluent(R)
    words,idx=ball(R,n,L)
    d=len(perms[0])
    P=[[p-1 for p in pm] for pm in perms]
    Pinv=[[0]*d for _ in P]
    for c,pm in enumerate(P):
        for i,j in enumerate(pm): Pinv[c][j]=i
    # check relators hold in the permutation rep
    for (x,y,z) in relators:
        assert all(P[z][P[y][P[x][i]]]==i for i in range(d))
    def act(w):
        i=0
        for c in w: i=P[c][i] if c<n else Pinv[c-n][i]
        return i
    Hs=[i for i,w in enumerate(words) if i>0 and act(w)==0]
    cls=[]
    for i in Hs:
        j=idx[R.reduce(inv(words[i],n))]
        if i<j: cls+= [[i,j],[-i,-j]]
    for i in Hs:
        for j in Hs:
            k=idx.get(R.reduce(words[i]+words[j]))
            if k is None: continue
            cls.append([-i,-j] if k==0 else [-i,-j,k])
    t=time.time(); res=[]
    for Sol in (Cadical153,Glucose4):
        with Sol(bootstrap_with=cls) as so: res.append(so.solve())
    assert res[0]==res[1]
    return dict(index=d,H_elements=len(Hs),clauses=len(cls),sat=res[0],secs=round(time.time()-t,2))
if __name__=="__main__":
    reps=json.load(open("q2_presentations.json")); Q=json.load(open(sys.argv[1]))
    L=int(sys.argv[2]); ks=sys.argv[3:] or [k for k in Q if k!="end"]
    for k in ks:
        for m,perms in enumerate(Q[k]):
            print(k,m,run_sub(7,reps[int(k)],perms,L),flush=True)
