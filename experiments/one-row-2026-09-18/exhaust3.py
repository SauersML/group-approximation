# Exhaustive over one-row pairs b=+1 on Z/n, c = R_th o swap(B,C) (all 3-break circle exchanges up to rotation of labels)
import sys
from prof import *; from repair import *
n=int(sys.argv[1]); W=int(sys.argv[2]); out=[]
for be in range(1,n-1):
  for ga in range(1,n-be):
    al=n-be-ga
    if al<1: continue
    for th in range(n):
        c=arcx(n,th,al,be,ga); p,a=profile(c,W,W)
        cand=sorted(set([0,al,al+be, th%n, (th+al)%n, (th+al+ga)%n]))
        cost,how=best_repair(c,cand,3)
        out.append((cost/p,cost,p,th,al,be,ga,how))
out.sort(reverse=True)
print('n',n,'pairs',len(out))
for r in out[:8]: print('ratio %.2f cost %d rho>=%.2f th=%d al=%d be=%d ga=%d %s'%r)
