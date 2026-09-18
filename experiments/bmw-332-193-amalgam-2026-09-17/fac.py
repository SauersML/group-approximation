# does the S3 map rho factor through the level-n quotient K_n?  (rho given as perms on 3 extra points)
import sys
from aut import perms
nm=sys.argv[1]; rho=eval(sys.argv[2]); NMAX=int(sys.argv[3])
print('ls:=[];;')
for n in range(1,NMAX+1):
    P=perms(nm,n); m=3**n
    g=[ 'PermList([' + ','.join(str(i+1) for i in P[a]) + ',' + ','.join(str(m+rho[a][j]+1) for j in range(3)) + '])' for a in range(4)]
    h=[ 'PermList([' + ','.join(str(i+1) for i in P[a]) + '])' for a in range(4)]
    print('G:=Group(%s);; H:=Group(%s);; Print(%d," ",Size(G)/Size(H),"\\n");'%(','.join(g),','.join(h),n))
