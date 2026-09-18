"""H4 (and H3 calibration) arrangement facts for Case 1 of the bottom-triple lemma.
Checks, exactly up to 1e-9 in floating point on the root system:
 (1) l_x (fixed line of W_X) is a modular line of A' = A_x u A_y: for any two walls
     w,w' of A'\A_x, the span (w cap w') + l_x is a wall of A_x.  => M(A') -> M(A_x)/l_x
     is a fibre bundle with fibre C minus |A_y\A_z| points, pi_1 M(A') = F_k x| P_X.
 (2) the monodromy points collide only along A_z walls (collision hyperplanes of the
     fibre points are exactly the A_z walls), so N_X = ker(P_X -> P_Z) acts trivially.
 (3) counts non-commuting codim-2 flats w cap w' with w in A_y\A_z, w' in A_x\A_z and the
     third walls through them (all outside A_x u A_y): these are the walls any useful
     auxiliary arrangement must add.
"""
import itertools, numpy as np
phi=(1+5**.5)/2
def refl(r,v): return v-2*np.dot(v,r)/np.dot(r,r)*r
def roots_from_simple(sim):
    R=[np.array(s,float) for s in sim]; out=[]
    todo=list(R)
    while todo:
        r=todo.pop()
        if any(np.allclose(r,q) for q in out): continue
        out.append(r)
        for s in R: todo.append(refl(s,r))
    return out
def walls(rs):
    W=[]
    for r in rs:
        r=r/np.linalg.norm(r)
        if not any(abs(abs(np.dot(r,w))-1)<1e-9 for w in W): W.append(r)
    return W
def setup(name):
    if name=='H4':  # s1-s2-s3=5=s4
        # Gram-matrix realisation: simple roots with <ai,aj>=-cos(pi/m)
        m={(0,1):3,(1,2):3,(2,3):5}; n=4
    else:           # H3: s1-s2=5=s3 (X={s2,s3}=I2(5), Y={s1,s2}=A2)
        m={(0,1):3,(1,2):5}; n=3
    G=np.eye(n)
    for i in range(n):
        for j in range(n):
            if i!=j: G[i,j]=-np.cos(np.pi/m.get((min(i,j),max(i,j)),2))
    L=np.linalg.cholesky(G); sim=[L[i] for i in range(n)]
    W=walls(roots_from_simple(sim))
    om=np.linalg.inv(np.array(sim)).T   # om[i]: <om_i,a_j>=delta_ij
    return n,sim,W,om
def through(W,pts):
    return [w for w in W if all(abs(np.dot(w,p))<1e-9 for p in pts)]
def is_wall(v,W):
    v=v/np.linalg.norm(v); return any(abs(abs(np.dot(v,w))-1)<1e-9 for w in W)
def normal_of_span(vecs):  # normal of hyperplane spanned by vecs (n-1 independent)
    u,s,vt=np.linalg.svd(np.array(vecs)); return vt[-1] if s[-1]<1e-9 or len(vecs)<vt.shape[0] else None
def run(name):
    n,sim,W,om=setup(name)
    x=om[0]; y=om[n-1]           # x: type s1-hat (W_X), y: type sn-hat (W_Y)
    Ax=through(W,[x]); Ay=through(W,[y]); Az=through(W,[x,y])
    Ap=walls(Ax+Ay); extra=[w for w in Ay if not any(abs(abs(np.dot(w,v))-1)<1e-9 for v in Ax)]
    print(name,'walls',len(W),'|A_x|',len(Ax),'|A_y|',len(Ay),'|A_z|',len(Az),"|A'|",len(Ap),'|A_y\\A_z|',len(extra))
    # (1) modularity: for w,w' in extra, flat F=w cap w' (dim n-2); F+l_x hyperplane must be a wall of A_x
    ok=True
    for w1,w2 in itertools.combinations(extra,2):
        # F + l_x has normal orthogonal to x and to F, i.e. normal in span(w1,w2) orthogonal to x
        a,b=np.dot(w1,x),np.dot(w2,x); nv=b*w1-a*w2
        if np.linalg.norm(nv)<1e-9: ok=False; continue
        if not is_wall(nv,Az): ok=False
    print(' (1)+(2) collisions of fibre points lie on A_z walls:',ok)
    # (3) non-commuting flats between A_y\A_z and A_x\A_z
    Axz=[w for w in Ax if not is_wall(w,Az)]
    stats={}; third=[]
    for w1 in extra:
        for w2 in Axz:
            sp=[w for w in W if abs(np.dot(w,np.cross(w1,w2)) if n==3 else 0)<1e-9] if n==3 else None
            # walls through w1 cap w2 = walls whose normal lies in span(w1,w2)
            B=np.array([w1,w2]); P=B.T@np.linalg.pinv(B.T)
            th=[w for w in W if np.linalg.norm(P@w-w)<1e-9]
            k=len(th); stats[k]=stats.get(k,0)+1
            if k>2:
                for w in th:
                    if not is_wall(w,Ap) and not is_wall(w,third): third.append(w)
    print(' pairs (w in A_y\\A_z, w\' in A_x\\A_z) by number of walls through w cap w\':',dict(sorted(stats.items())))
    print(' distinct walls outside A_x u A_y through non-commuting such flats:',len(third))
if __name__=="__main__":
    for nm in ["H3","H4"]: run(nm)
