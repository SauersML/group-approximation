"""For each non-commuting flat V = w cap w' (w in A_y\A_z, w' in A_x\A_z), form
B = A_x u A_y u A_V and test: (a) is l_x still modular in B (fibre bundle over M(A_x)/l_x)?
(b) along which walls of A_x do the fibre points collide?  If all collisions lie on A_z
walls, N = ker(P_X->P_Z) still acts trivially on the fibre group and B is as blind as A'.
Run after fibred.py (imports its helpers)."""
import itertools, numpy as np
from fibred import setup, through, walls, is_wall
def run(name):
    n,sim,W,om=setup(name); x=om[0]; y=om[n-1]
    Ax=through(W,[x]); Ay=through(W,[y]); Az=through(W,[x,y])
    Ap=walls(Ax+Ay); Ayz=[w for w in Ay if not is_wall(w,Az)]; Axz=[w for w in Ax if not is_wall(w,Az)]
    seen=[]
    for w1 in Ayz:
        for w2 in Axz:
            B2=np.array([w1,w2]); P=B2.T@np.linalg.pinv(B2.T)
            AV=[w for w in W if np.linalg.norm(P@w-w)<1e-9]
            if len(AV)==2: continue
            key=sorted(round(float(abs(v)),6) for v in P.flatten())
            B=walls(Ap+AV); fib=[w for w in B if abs(np.dot(w,x))>1e-9]
            modular=True; hits=set()
            for u,v in itertools.combinations(fib,2):
                a,b=np.dot(u,x),np.dot(v,x); nv=b*u-a*v
                if np.linalg.norm(nv)<1e-9: continue
                if not is_wall(nv,Ax): modular=False
                elif not is_wall(nv,Az): hits.add(tuple(np.round(nv/np.linalg.norm(nv)*np.sign(nv[np.argmax(abs(nv))]),6)))
            print(name,'type',{3:'A2',5:'I2(5)'}[len(AV)],'|B|',len(B),'fibre pts',len(fib),
                  'l_x modular',modular,'collision walls outside A_z',len(hits))
for nm in ['H3','H4']: run(nm)
