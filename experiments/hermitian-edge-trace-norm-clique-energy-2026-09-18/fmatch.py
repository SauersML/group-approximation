import numpy as np, sys, itertools
from scipy.optimize import minimize
m=int(sys.argv[1]); k=m  # vectors in C^m: covers every unit-diagonal PSD G
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 0)
V=list(range(m))
# vertices of fractional perfect matching polytope: perfect matchings + odd cycles (1/2)
def fpm_vertices(verts):
    if not verts: yield {} ; return
    v=verts[0]; rest=verts[1:]
    for u in rest:  # edge v-u
        r2=[w for w in rest if w!=u]
        for s in fpm_vertices(r2):
            s2=dict(s); s2[(min(u,v),max(u,v))]=s2.get((min(u,v),max(u,v)),0)+1; yield s2
    for L in range(3,len(verts)+1,2):  # odd cycle through v
        for others in itertools.permutations(rest,L-1):
            if others[0]>others[-1]: continue
            cyc=(v,)+others
            r2=[w for w in rest if w not in others]
            for s in fpm_vertices(r2):
                s2=dict(s)
                for a,b in zip(cyc,cyc[1:]+cyc[:1]):
                    e=(min(a,b),max(a,b)); s2[e]=s2.get(e,0)+0.5
                yield s2
iu=[(i,j) for i in range(m) for j in range(i+1,m)]
Y=[]
for s in fpm_vertices(V):
    Y.append([s.get(e,0) for e in iu])
Y=np.unique(np.array(Y),axis=0); print("vertices",len(Y))
def rvec(x):
    U=(x[:m*k]+1j*x[m*k:2*m*k]).reshape(m,k)
    U=U/np.linalg.norm(U,axis=1)[:,None]; G=U@U.conj().T
    return np.array([1/np.abs(1-G[i,j]) for (i,j) in iu])
def obj(z): return z[-1]
cons=[{'type':'ineq','fun':lambda z: z[-1]-2*Y@rvec(z[:-1])}]
best=1e9
for t in range(40):
    x0=rng.normal(size=2*m*k); z0=np.append(x0,2*np.max(Y@rvec(x0))+0.1)
    r=minimize(obj,z0,constraints=cons,method='SLSQP',options={'maxiter':2000})
    if r.success or True:
        val=2*np.max(Y@rvec(r.x[:-1]))
        best=min(best,val)
print(m,"min 2nu_f=%.5f target=%.5f ratio=%.4f"%(best,np.sqrt(3)/2*(m-1),best/(np.sqrt(3)/2*(m-1))))
