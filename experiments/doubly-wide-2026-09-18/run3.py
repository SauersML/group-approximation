from prof import profile
from onesided import onesided,cylinders
from excised import excised
import sys
for a in [5,7,9,11,13]:
  W=a*a+1
  for k in [1,2,3]:
    b,c=excised(W,a,k)
    p,arg=profile(b,c,int(sys.argv[1]) if len(sys.argv)>1 else 2*a)
    print(f"W={W} a={a} k={k} rho_hat={p:.2f}@{arg} Hcyl={cylinders(b,c)} Vcyl={cylinders(c,b)} H1side={onesided(b,c)} V1side={onesided(c,b)}",flush=True)
