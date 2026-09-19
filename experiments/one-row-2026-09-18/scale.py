import random, math
from prof import *
random.seed(7)
for n in [100,300,900,2000]:
    W=int(2*math.sqrt(n))+5; vals=[]
    for tr in range(4):
        ga=n//3; al=n-1-ga; th=random.randint(n//5,4*n//5)
        p,a=profile(arcx(n,th,al,1,ga),W,W); vals.append((round(p,2),th,a))
    print(n,W,vals,flush=True)
