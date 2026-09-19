# Checks the exact statements of one-row-profile-pairs-need-arc-tori-not-rotations.
# (1) theta=0: c fixes A pointwise (alpha points), moves all L=beta+gamma points of B u C,
#     and |B_t| <= 3 for all t; the two-row pair (b cut at 2 points, c) commutes.
# (2) theta=L: c'(x)=x+L on Z/(n+beta) (padding n..n+beta-1 after n-1) agrees with c off B.
# (3) profile (moved-count version) <= sup_t |B_t| on random 3-arc exchanges.
import numpy as np, random
from prof import arcx, profile
def breaks(ct):
    n=len(ct); x=np.arange(n); return int(np.count_nonzero(ct[(x+1)%n]!=(ct[x]+1)%n))
bad=0
for n in range(6,41):
    for al in range(1,n-1):
        for be in range(1,n-al):
            ga=n-al-be; L=be+ga
            c=arcx(n,0,al,be,ga); x=np.arange(n)
            if np.count_nonzero(c==x)!=al: bad+=1
            ct=x.copy(); mb=0
            for t in range(1,L+1):
                ct=c[ct]; mb=max(mb,breaks(ct))
            if mb>3: bad+=1
            b2=(x+1)%n; b2[al-1]=0; b2[n-1]=al       # rows A and B u C
            if not np.array_equal(b2[c],c[b2]): bad+=1
            c=arcx(n,L,al,be,ga); N=n+be
            cp=(x+L)%N; Bm=(x>=al)&(x<al+be)
            if not np.array_equal(cp[~Bm],c[~Bm]): bad+=1
print('exact checks n=6..40, failures:',bad)
random.seed(1); worst=0
for trial in range(60):
    n=random.randint(30,120); al=random.randint(1,n-2); be=random.randint(1,n-al-1); ga=n-al-be
    th=random.randrange(n); c=arcx(n,th,al,be,ga); x=np.arange(n)
    ct=x.copy(); mb=0
    for t in range(1,31):
        ct=c[ct]; mb=max(mb,breaks(ct))
    p,_=profile(c,30,30); worst=max(worst,p/mb)
print('max profile/sup|B_t| over 60 random (s,t<=30):',round(worst,3))
