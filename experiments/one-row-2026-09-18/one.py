import sys
from prof import *
n,th,al,be,ga,W=map(int,sys.argv[1:7])
c=arcx(n,th,al,be,ga)
print(profile(c,W,W))
# cycle structure of c
seen=[0]*n; cyc=[]
for x in range(n):
    if not seen[x]:
        L=0;y=x
        while not seen[y]: seen[y]=1;y=c[y];L+=1
        cyc.append(L)
print('c cycles',sorted(cyc))
