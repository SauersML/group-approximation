import numpy as np, itertools, sys, random
n=int(sys.argv[1]); trials=int(sys.argv[2]); dens=float(sys.argv[3])
import os
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'search3.py')).read()
body=src.split("ess=[")[0].replace("n=int(sys.argv[1]) if len(sys.argv)>1 else 3","n=%d"%n)
exec(body)
fns=src.split("print(\"primitive essential:\",len(ess))")[1].split("cnt_nocone=0")[0]
exec(fns)
inv={'a':'A','A':'a','b':'B','B':'b'}
def bad_word(Ma,Mb):
    E={'a':rel(Ma),'A':rel(Ma.T),'b':rel(Mb),'B':rel(Mb.T)}
    full=frozenset((i,j) for i in range(n) for j in range(n))
    succ={e:{} for e in E}
    for e in E:
        for (i,j) in E[e]: succ[e].setdefault(i,set()).add(j)
    mul=lambda R,e: frozenset((i,k) for (i,j) in R for k in succ[e].get(j,()))
    for L in range(1,7):
        for u in itertools.product('aAbB',repeat=L):
            w=''.join(u); ww=w+w
            if any(ww[i]==inv[ww[i+1]] for i in range(len(ww)-1)): continue
            R=E[w[0]]
            for e in (w*40)[1:]: R=mul(R,e)
            if R!=full: return w
    return 'none<=6'
rng=np.random.default_rng(int(sys.argv[4]) if len(sys.argv)>4 else 1)
from collections import Counter
cnt=Counter(); hits=[]
def rand():
    while True:
        M=(rng.random((n,n))<dens).astype(np.int64)
        if M.sum(1).min()>0 and M.sum(0).min()>0 and primitive(M): return M
for t in range(trials):
    Ma=rand(); Mb=rand()
    if cones_meet(Ma,Mb): continue
    ok=path_ok(Ma,Mb)
    if ok:
        hits.append((Ma.tolist(),Mb.tolist())); cnt['PATHOK']+=1
    else:
        cnt[bad_word(Ma,Mb)]+=1
print(cnt)
for h in hits[:5]: print(h)
