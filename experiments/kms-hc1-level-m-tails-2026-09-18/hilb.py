import sys
# PBW dims of u(L_p), L_p = n+ + t sl3[t]; multidegree (a,b,c) with a=alpha1,b=alpha2,c=alpha0=delta-a1-a2
p=int(sys.argv[1]); box=tuple(int(x) for x in sys.argv[2:5])
roots=[]
# finite roots as (n1,n2) coefficients; element X t^k has multidegree  k*(1,1,1) + (n1,n2,0) - adjusted
fin={(1,0):1,(0,1):1,(1,1):1,(-1,0):1,(0,-1):1,(-1,-1):1,(0,0):2}
for k in range(0,40):
    for (n1,n2),mult in fin.items():
        if k==0 and not (n1>=0 and n2>=0 and (n1,n2)!=(0,0)): continue
        d=(k+n1,k+n2,k)
        if all(d[i]<=box[i] for i in range(3)) and min(d)>=0:
            roots+= [d]*mult
from collections import defaultdict
H=defaultdict(int); H[(0,0,0)]=1
for r in roots:
    NH=defaultdict(int)
    for d,v in H.items():
        for e in range(p):
            nd=(d[0]+e*r[0],d[1]+e*r[1],d[2]+e*r[2])
            if all(nd[i]<=box[i] for i in range(3)): NH[nd]+=v
            else: break
    H=NH
print(len(roots),"roots; dim at box",H[box],"total",sum(H.values()))
