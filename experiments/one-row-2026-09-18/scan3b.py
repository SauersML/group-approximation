import sys, random
from prof import *; from repair import *
random.seed(int(sys.argv[4])); n=int(sys.argv[1]); W=int(sys.argv[2])
for trial in range(int(sys.argv[3])):
    be=random.randint(1,n//3); ga=random.randint(1,n//3); al=n-be-ga
    th=random.choice([random.randint(0,n-1), be+random.randint(-4,4), n-ga+random.randint(-4,4), random.randint(1,int(n**.5)+3)])%n
    c=arcx(n,th,al,be,ga); p,a=profile(c,W,W)
    cand=[0,al,al+be, th%n, (th+al)%n, (th+al+ga)%n]
    cost,how=best_repair(c,cand,6)
    print("rho>=%.2f cost<=%d ratio %.2f  th=%d al=%d be=%d ga=%d %s"%(p,cost,cost/p,th,al,be,ga,how),flush=True)
