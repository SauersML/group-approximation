import sys
from swap import *
from lib import profile as prof
import numpy as np
def exc(a,k):
    W=a*a+1; keep=[x for x in range(W) if x>=k]; idx={x:i for i,x in enumerate(keep)}; n=len(keep)
    c=[]
    for x in keep:
        y=(x+a)%W
        while y<k: y=(y+a)%W
        c.append(idx[y])
    return n,c
for a,k in [(5,1),(7,1),(7,2),(9,2),(11,3)]:
    n,c=exc(a,k); b=[(x+1)%n for x in range(n)]
    S=Surf(b,c); r,_=prof(np.array(c),20,20)
    print(a,k,n,'excess',excess(b,c),'rho^%.2f'%r, 'swap',best_swap(S,11,first=True) and best_swap(S,11)[:3],flush=True)
