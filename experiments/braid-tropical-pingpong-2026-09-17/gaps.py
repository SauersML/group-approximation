import pickle, sys, math
from troplib import eig_vals, intervals
res=pickle.load(open(sys.argv[1],'rb'))
M=720; out={}
for s in range(M):
    th=2*math.pi*s/M; w=(math.cos(th),math.sin(th))
    gaps=set(range(1,6)); wit={}
    for x,cp in res.items():
        ev=eig_vals(cp,w)
        for k in list(gaps):
            if abs(ev[k]-ev[k-1])<1e-9: gaps.discard(k); wit[k]=x
    out[s]=(gaps,wit)
for k in range(1,6):
    print('gap',k,'uniform on rays (deg):',[(a/2,b/2) for a,b in intervals([s for s in out if k in out[s][0]])])
