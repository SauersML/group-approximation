import sys, json, numpy as np
from init_models import *
from higman_hs_search import flow, edges
topo=sys.argv[1]; k=int(sys.argv[2]); iters=int(sys.argv[3]); ps=[int(x) for x in sys.argv[4:]]
for p in ps:
    g,M,T,K=homogeneous_init(p,k)
    g,val,res,hist=flow(g,edges(topo,k),iters,frozen=(0,),log_every=max(1,iters//5))
    mark=[2-2*np.trace(x).real/p for x in g]
    print(json.dumps(dict(p=p,topo=topo,k=k,delta2=val,res=[round(r,5) for r in res],mark2=[round(m,3) for m in mark],hist=[(h[0],round(h[1],5)) for h in hist])),flush=True)
