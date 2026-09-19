# full rank profile (all s,t <= n; early break n/(s+t) <= best) and best-rotation agreement cost, for listed pairs
import sys, numpy as np
from lib import arcx
from rankprof import rankprof
for line in sys.stdin:
    n,th,al,be,ga=map(int,line.split()[:5]); c=arcx(n,th,al,be,ga)
    lam,arg=rankprof(c,n); x=np.arange(n)
    rot=n-max(np.bincount((c-x)%n,minlength=n))
    print(n,th,al,be,ga,'lam %.3f'%lam,arg,'rotcost',rot,flush=True)
