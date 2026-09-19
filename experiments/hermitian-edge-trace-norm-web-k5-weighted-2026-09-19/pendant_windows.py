# pendant_windows.py (lane w11-078, 2026-09-19): which open webs C_n^k (k = 5, 6, 7) the weighted window
# H = K_5 plus a pendant vertex closes, given c(H, w) >= 6.23539 for w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)
# (hermitian-edge-trace-norm-web-rank-k4-n13-n14).  The window is U_t = {t, .., t+4, t+k+4}; for each n the script
# checks that U_t induces exactly H (K_5 on t..t+4, t+k+4 adjacent to t+4 only) and the six points are distinct,
# and then tests  n c / |w| >= sqrt3 (n - floor(n/(k+1)))  exactly in rationals (squared, both sides >= 0).
from fractions import Fraction as F
c=F('6.23539'); w=[F(3,4)]*4+[F(1),F(1,5)]; W=sum(w)
H={(a,b) for a in range(5) for b in range(a+1,5)}|{(4,5)}
OPEN={5:[13,14,15,16,17,20,21,22,23,26,27,28,29,32,33,34,35,39,40,41,45,46,47,51,52,53,58,59,64,65,70,71,77,83,89],
      6:[17,18,19,20,25,26,27,34], 7:[22,23]}
def dist(a,b,n): d=(a-b)%n; return min(d,n-d)
for k,ns in OPEN.items():
    closed=[]; left=[]
    for n in ns:
        U=[0,1,2,3,4,k+4]
        ok=len({u%n for u in U})==6 and {(a,b) for a in range(6) for b in range(a+1,6) if 1<=dist(U[a],U[b],n)<=k}==H
        rhs=n-n//(k+1); good=ok and (n*c/W)**2>=3*rhs**2
        (closed if good else left).append(n)
        print("k=%d n=%3d window induces H: %s  n c/|w| = %.5f  sqrt3(n-floor(n/(k+1))) = %.5f  %s"%(
            k,n,ok,float(n*c/W),3**.5*rhs,"CLOSED" if good else "open"))
    print("k=%d closed %d of %d: %s ; still open: %s"%(k,len(closed),len(ns),closed,left))
# For n = 13, 14 (k = 5) no 6-subset of Z_n induces H at all (11 edges, degrees 1,4,4,4,4,5 characterise H).
import itertools
for n in (13,14):
    cnt=0
    for S in itertools.combinations(range(1,n),5):
        S=(0,)+S; E=[(a,b) for a in range(6) for b in range(a+1,6) if 1<=dist(S[a],S[b],n)<=5]
        if len(E)==11 and sorted(sum(v in e for e in E) for v in range(6))==[1,4,4,4,4,5]: cnt+=1
    print("k=5 n=%d: 6-subsets containing 0 that induce H: %d"%(n,cnt))
