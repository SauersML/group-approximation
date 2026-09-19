import sys, random
from prof import *; from repair import *
random.seed(5); n=int(sys.argv[1])
for trial in range(int(sys.argv[2])):
    be=random.randint(1,2); ga=random.randint(n//5,n//2); al=n-be-ga; th=random.randint(0,n-1)
    c=arcx(n,th,al,be,ga); p,a=profile(c,30,30)
    cand=[0,al,al+be, th%n, (th+al)%n, (th+al+ga)%n]
    cost,how=best_repair(c,cand,4)
    print("rho>=%.2f cost<=%d th=%d al=%d be=%d ga=%d %s"%(p,cost,th,al,be,ga,how),flush=True)
