import sys; sys.path.insert(0,'.')
from roots import *
import numpy as np
for name,ms in [('H4',M(4,{(0,1):3,(1,2):3,(2,3):5})),('H4r',M(4,{(0,1):5,(1,2):3,(2,3):3})),('A4',M(4,{(0,1):3,(1,2):3,(2,3):3})),('B4',M(4,{(0,1):3,(1,2):3,(2,3):4}))]:
    R,B=roots(ms); n=4
    # work in root coordinates with bilinear form B; hyperplane of root r = {x: r.B.x=0}; normals nr = B r (covectors)
    Nv=np.array([B@r for r in R])
    # line L = fixed by s2,s3,s4 = {x : e_j.B.x=0 for j=1,2,3} 
    X=[1,2,3]
    L=np.linalg.svd(Nv[[0,1,2,3]][X])[2][-1]  # simple root indices 1..3 are rows 1,2,3 of R (simple first)
    inX=[i for i in range(len(R)) if abs(Nv[i]@L)<1e-9]
    out=[i for i in range(len(R)) if i not in inX]
    bad=0
    for i,j in itertools.combinations(out,2):
        # H_i cap H_j + L hyperplane: covector c in span(N_i,N_j) with c.L=0
        c=Nv[i]*(Nv[j]@L)-Nv[j]*(Nv[i]@L)
        c/=np.linalg.norm(c)
        if not any(abs(abs(c@(Nv[k]/np.linalg.norm(Nv[k])))-1)<1e-7 for k in inX): bad+=1
    print(name,len(R),'X-walls',len(inX),'nonmodular pairs',bad)
