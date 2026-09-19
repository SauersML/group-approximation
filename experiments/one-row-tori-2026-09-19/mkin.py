# print chain2 input for the one-row 3-arc pair (n th al be ga), optionally with a w x h donor torus
import sys
from lib import arcx
n,th,al,be,ga=map(int,sys.argv[1:6]); w,h=(int(sys.argv[6]),int(sys.argv[7])) if len(sys.argv)>7 else (0,0)
c=arcx(n,th,al,be,ga).tolist(); b=[(x+1)%n for x in range(n)]
for j in range(h):
    for i in range(w):
        x=n+j*w+i; b.append(n+j*w+(i+1)%w); c.append(n+((j+1)%h)*w+i)
print(len(b)); print(*b); print(*c)
