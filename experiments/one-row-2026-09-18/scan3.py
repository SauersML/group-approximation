import sys, numpy as np, random
from prof import *
random.seed(1)
n=int(sys.argv[1]); S=T=int(sys.argv[2])
rows=[]
for trial in range(int(sys.argv[3])):
    be=random.randint(1,n//3); ga=random.randint(1,n//3); al=n-be-ga; th=random.randint(0,n-1)
    p,a=profile(arcx(n,th,al,be,ga),S,T)
    rows.append((p,th,al,be,ga,a))
rows.sort()
for r in rows[:12]: print("%.2f th=%d al=%d be=%d ga=%d arg=%s"%r)
print('...'); 
for r in rows[-3:]: print("%.2f th=%d al=%d be=%d ga=%d arg=%s"%r)
