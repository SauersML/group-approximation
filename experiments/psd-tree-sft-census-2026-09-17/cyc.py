import numpy as np, itertools, sys
import os
src=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'search3.py')).read()
src=src.split("cnt_nocone=0")[0].replace("n=int(sys.argv[1]) if len(sys.argv)>1 else 3","n=3")
exec(src)
inv={'a':'A','A':'a','b':'B','B':'b'}
def find_cycle(Ma,Mb):
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
            for e in (w*30)[1:]: R=mul(R,e)
            if R!=full: return w
    return None
from collections import Counter
out=[]
for (ba,Ma) in ess:
    for (bb,Mb) in ess:
        if cones_meet(Ma,Mb): continue
        out.append(find_cycle(Ma,Mb))
print(Counter(out))
