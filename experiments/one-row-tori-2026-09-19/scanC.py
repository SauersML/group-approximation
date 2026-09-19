# random one-row 3-arc pairs: rank profile Lambda^ (s,t<=W), excision m (<=mmax), C slit-swap search (L<=Lmax)
import sys, random, subprocess
from lib import arcx
from rankprof import rankprof
from excrep import mtab, key
seed,n,N,W,Lmax,mmax=map(int,sys.argv[1:7]); rng=random.Random(seed)
tab=mtab(n,mmax) if mmax>0 else {}
for it in range(N):
    al=rng.randrange(1,n-1); be=rng.randrange(1,n-al)
    ga=n-al-be
    if ga<1: continue
    th=rng.randrange(n); c=arcx(n,th,al,be,ga)
    lam,arg=rankprof(c,W); m=tab.get(key(c)) if mmax>0 else None
    inp='%d\n%s\n%s\n'%(n,' '.join(str((x+1)%n) for x in range(n)),' '.join(map(str,c.tolist())))
    out=subprocess.run(['./chain2','0',str(Lmax)],input=inp,capture_output=True,text=True).stdout.split('\n')[0].split()
    L,cost=int(out[5]),int(out[7])
    print(n,th,al,be,ga,'%.3f'%lam,arg,'m',m,'swapL',L,'cost',cost,flush=True)
