"""N-word length of d = s3^-1 s4^2 s3 in the meridian generators of N (dumpgen.py letters), by meet in the middle."""
import sys
sys.path.insert(0,'/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
from garside import Coxeter, Artin
from search import DIAGRAMS
name=sys.argv[1]; R=int(sys.argv[2])
n,md=DIAGRAMS[name]; W=Coxeter(n,md); G=Artin(W)
full=(1<<n)-1; X=full&~1; Y=full&~(1<<(n-1)); Z=X&Y
def mer(T):
    order=sorted([w for w in range(W.N) if W.supp[w]&~T==0],key=lambda w:(W.length[w],W.word[w]))
    seen={}
    for w in order:
        for s in range(n):
            if not (T>>s)&1 or W.length[W.rmul[w][s]]<W.length[w]: continue
            r=W.mul(W.rmul[w][s],W.inv[w])
            if r in seen or W.supp[r]&~Z==0: continue
            seen[r]=[i+1 for i in W.word[w]]+[s+1,s+1]+[-(i+1) for i in reversed(W.word[w])]
    return list(seen.values())
NW=mer(X); gens=[]
for wd in NW: gens+= [G.word(wd), G.inv(G.word(wd))]
key=lambda g:(g[0],tuple(g[1]))
ball={key(G.one):0}; front=[G.one]
for r in range(1,R+1):
    nf=[]
    for g in front:
        for h in gens:
            x=G.mul(g,h); kx=key(x)
            if kx not in ball: ball[kx]=r; nf.append(x)
    front=nf
print(name,'N-letters',len(NW),'ball',R,len(ball))
d=G.word([-(n-1),n,n,n-1])
best=None
for g,rg in list(ball.items()):
    x=G.mul(d,G.inv((g[0],list(g[1])))); kx=key(x)
    if kx in ball:
        t=rg+ball[kx]
        if best is None or t<best: best=t
print('length of d <=',best,'(None = >',2*R,')')
