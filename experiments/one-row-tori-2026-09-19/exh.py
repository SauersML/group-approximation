# exhaustive 3-arc circle exchanges on Z/n: cheap profile lower bound rho^ (s,t<=W), keep rho^<=cut
import sys, numpy as np
from lib import arcx
n=int(sys.argv[1]); W=int(sys.argv[2]); cut=float(sys.argv[3])
x=np.arange(n)
def prof(c):
    best=0; ct=x.copy()
    for t in range(1,W+1):
        ct=c[ct]
        for s in range(1,W+1):
            m=np.count_nonzero(ct[(x+s)%n]!=(ct+s)%n)
            v=m/(s+t)
            if v>best:
                best=v
                if best>cut: return best
    return best
cnt=0
for al in range(1,n-1):
  for be in range(1,n-al):
    ga=n-al-be
    for th in range(n):
        c=arcx(n,th,al,be,ga)
        r=prof(c)
        if r<=cut: print(th,al,be,ga,'%.3f'%r); cnt+=1
print('#kept',cnt,file=sys.stderr)
