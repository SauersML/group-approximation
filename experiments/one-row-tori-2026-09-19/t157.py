import sys, time
from swap import *
from lib import arcx
n,th,al,be,ga=map(int,sys.argv[1:6]); Lmax=int(sys.argv[6])
c=arcx(n,th,al,be,ga).tolist(); b=[(x+1)%n for x in range(n)]
S=Surf(b,c); print('excess',excess(b,c),'cones',[len(S.cls[v])//4 for v in S.cones()])
t0=time.time()
r=best_swap(S,Lmax,first=True)
if r is None: print('none up to',Lmax,time.time()-t0)
else:
    L,cst,ex,b2,c2,w,v=r; print('L',L,'cost',cst,'newexcess',ex,'word',w,time.time()-t0)
    if ex>0:
        print('greedy',greedy(b,c,Lmax))
