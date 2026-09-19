import random
from prof import *; from repair import *
random.seed(3); n=500
for tr in range(6):
    be=random.randint(1,4); ga=random.randint(10,120); al=n-be-ga; th=be+ga
    c=arcx(n,th,al,be,ga); p,a=profile(c,50,50)
    cand=[0,al,al+be, th%n, (th+al)%n, (th+al+ga)%n]
    cost,how=best_repair(c,cand,5)
    print("rho>=%.2f cost<=%d th=%d al=%d be=%d ga=%d %s %s"%(p,cost,th,al,be,ga,a,how),flush=True)
