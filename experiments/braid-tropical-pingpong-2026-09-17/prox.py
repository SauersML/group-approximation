import pickle, sys, math, collections
from troplib import eig_vals, intervals
res=pickle.load(open(sys.argv[1],'rb'))
M=720; bad={}
for s in range(M):
    th=2*math.pi*s/M; w=(math.cos(th),math.sin(th))
    for x,cp in res.items():
        ev=eig_vals(cp,w)
        if abs(ev[0]-ev[1])<1e-9 or abs(ev[-1]-ev[-2])<1e-9:
            bad.setdefault(s,[]).append(x)
good=[s for s in range(M) if s not in bad]
print('proximal-for-all rays (deg):',[(a/2,b/2) for a,b in intervals(good)])
for s in [0,45,90,135,180,225,270,315]:
    if s*2 in bad: print(s, sorted(bad[2*s],key=len)[:5])
