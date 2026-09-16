import sys; sys.path.insert(0,'.')
from lp import *
m=int(sys.argv[1]); L=int(sys.argv[2])
def power(A,e):
    R=ident()
    for _ in range(e): R=mmul(R,A)
    return R
gens={'F':power(f,m),'f':power(fi,m),'K':power(k,m),'k':power(ki,m)}
inv={'F':'f','f':'F','K':'k','k':'K'}
from collections import Counter
level=[('',ident())]
for length in range(1,L+1):
    new=[]; stats=Counter()
    for w,M in level:
        for g in 'FfKk':
            if w and inv[w[-1]]==g: continue
            N=mmul(M,gens[g]); new.append((w+g,N))
            stats[cartan(N)]+=1
    level=new
    print(length, sorted(stats.items()))
