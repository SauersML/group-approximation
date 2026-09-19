# Collision walls D_E = E + L_X for bad rank-2 flats E (no X-wall through E), and which involve F-walls.
import sys, itertools, numpy as np
sys.path.insert(0,'.'); from roots import roots, M
T={'H4':(M(4,{(0,1):3,(1,2):3,(2,3):5}),[1,2,3],[0,1,2]),
   'H3':(M(3,{(0,1):3,(1,2):5}),[1,2],[0,1]),
   'A4':(M(4,{(0,1):3,(1,2):3,(2,3):3}),[1,2,3],[0,1,2]),
   'B3':(M(3,{(0,1):3,(1,2):4}),[1,2],[0,1]),
   'B4':(M(4,{(0,1):3,(1,2):3,(2,3):4}),[1,2,3],[0,1,2])}
def nrm(c):
    c=c/np.linalg.norm(c); k=np.argmax(abs(c)>1e-9); return c*np.sign(c[k])
def run(name):
    ms,X,Y=T[name]; R,B=roots(ms); n=len(ms); Nv=np.array([B@r for r in R])
    def fixline(S):
        return np.linalg.svd(Nv[S])[2][len(S):]
    LX=fixline(X); LY=fixline(Y)
    inX=[i for i in range(len(R)) if np.all(abs(Nv[i]@LX.T)<1e-9)]
    inY=[i for i in range(len(R)) if np.all(abs(Nv[i]@LY.T)<1e-9)]
    Fw=[i for i in inY if i not in inX]; out=[i for i in range(len(R)) if i not in inX]
    L=LX[0]
    # rank-2 flats among all hyperplanes: group pairs
    flats={}
    for i,j in itertools.combinations(range(len(R)),2):
        key=None
        for f in flats:
            A=Nv[list(f)[:2]]
            if np.linalg.matrix_rank(np.vstack([A,Nv[i],Nv[j]]),1e-7)==2: key=f;break
        if key is None: flats[frozenset((i,j))]=1
        else:
            nk=key|{i,j}; del flats[key]; flats[nk]=1
    bad=[f for f in flats if not (f & set(inX))]
    D={}
    for f in bad:
        i,j=list(f)[:2]; c=nrm(Nv[i]*(Nv[j]@L)-Nv[j]*(Nv[i]@L)); key=tuple(np.round(c,6))
        D.setdefault(key,[]).append(sorted(f))
    npairs=sum(len(f)*(len(f)-1)//2 for f in bad)
    print(name,'roots',len(R),'Xwalls',len(inX),'Fwalls',Fw,'bad flats',len(bad),'sizes',sorted(len(f) for f in bad).count(2),
          [sorted(len(f) for f in bad).count(s) for s in (3,4,5)],'bad pairs',npairs,'D-walls',len(D))
    print('  D-wall multiplicities (#bad flats per D-wall):',sorted(len(v) for v in D.values()))
    fb=[f for f in bad if f & set(Fw)]
    print('  bad flats meeting F-walls:',len(fb), [sorted(f) for f in fb][:12])
    return R,Nv,inX,Fw,bad,D
if __name__=='__main__':
    for nm in sys.argv[1:]: run(nm)
