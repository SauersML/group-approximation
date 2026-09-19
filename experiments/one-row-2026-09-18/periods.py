import sys, numpy as np
from prof import *
n,th,al,be,ga,Q=map(int,sys.argv[1:7])
c=arcx(n,th,al,be,ga); x=np.arange(n); ct=x.copy(); res=[]
for q in range(1,Q+1):
    ct=c[ct]; d=(ct-x)%n
    vals,cnt=np.unique(d,return_counts=True)
    for v,k in zip(vals,cnt):
        p=v if v<=n//2 else v-n
        res.append((k, p, q))
res.sort(reverse=True)
for k,p,q in res[:15]:
    print('q=%d p=%d fixed-by b^-p c^q: %d  (|p|+q=%d)'%(q,p,k,abs(p)+q))
