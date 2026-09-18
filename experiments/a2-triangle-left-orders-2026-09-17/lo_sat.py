# Positive-cone SAT search on the ball of radius L (normal forms from a confluent RWS).
import json, sys, itertools, time
from kb import RWS, inv
from pysat.solvers import Cadical153, Glucose4
def check_confluent(R):
    for l1,r1 in R.rules.items():
        for l2,r2 in R.rules.items():
            for k in range(1,min(len(l1),len(l2))):
                if l1[-k:]==l2[:k]:
                    if R.reduce(r1+l2[k:])!=R.reduce(l1[:-k]+r2): return False
    return True
def ball(R,n,L):
    words=[()]; layer=[()]; allw={():0}
    for d in range(L):
        nl=[]
        for w in layer:
            for c in range(2*n):
                v=R.reduce(w+(c,))
                if v not in allw: allw[v]=len(words); words.append(v); nl.append(v)
        layer=nl
    return words,allw
def run(n,relators,L,L1):
    R=RWS(n,relators).complete(10,verbose=False)
    conf=check_confluent(R)
    words,idx=ball(R,n,L)
    N=len(words)
    var=lambda i:i  # element i>0 -> var i
    cls=[]; ncl=0
    class S:
        def add_clause(self,c): cls.append(c)
    s=S()
    for i,w in enumerate(words):
        if i==0: continue
        j=idx[R.reduce(inv(w,n))]
        if j==0: raise Exception("torsion-like: nontrivial word equals identity?")
        if i<j: s.add_clause([i,j]); s.add_clause([-i,-j]); ncl+=2
    short=[i for i,w in enumerate(words) if 0<len(w)<=L1]
    for i in short:
        wi=words[i]
        for j in range(1,N):
            v=R.reduce(wi+words[j])
            k=idx.get(v)
            if k is None: continue
            if k==0: s.add_clause([-i,-j])
            else: s.add_clause([-i,-j,k])
            ncl+=1
    # torsion: word equal to itself squared etc are captured via products
    t=time.time()
    res=[]
    for Sol in (Cadical153,Glucose4):
        with Sol(bootstrap_with=cls) as so: res.append(so.solve())
    assert res[0]==res[1]; sat=res[0]
    return dict(confluent=conf,rules=len(R.rules),elements=N,clauses=ncl,sat=sat,secs=round(time.time()-t,2))
if __name__=="__main__":
    reps=json.load(open("q2_presentations.json"))
    L=int(sys.argv[1]); L1=int(sys.argv[2])
    ks=[int(a) for a in sys.argv[3:]] or range(len(reps))
    for k in ks:
        print(k, "torsion" if any(a==b==c for a,b,c in reps[k]) else "tf", run(7,reps[k],L,L1),flush=True)
