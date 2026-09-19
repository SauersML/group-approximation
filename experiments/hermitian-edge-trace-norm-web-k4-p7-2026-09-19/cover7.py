# 7-vertex windows of C_n^4 (n = 13, 14, 19) with at least MINE edges: numerical upper bounds on c.
import sys, itertools, numpy as np, networkx as nx
from cover import web, cmin
mine=int(sys.argv[1]); rest=int(sys.argv[2]); reps={}
for n in (13,14,19):
    E=web(n)
    for r in itertools.combinations(range(1,n),6):
        W=(0,)+r; G=nx.Graph(); G.add_nodes_from(range(7))
        G.add_edges_from((a,b) for a in range(7) for b in range(a+1,7) if (W[a],W[b]) in E)
        if G.number_of_edges()<mine: continue
        h=nx.weisfeiler_lehman_graph_hash(G,iterations=4); lst=reps.setdefault((G.number_of_edges(),h),[])
        if not any(nx.is_isomorphic(G,H) for H,_ in lst): lst.append((G,(n,W)))
cl=[x for l in reps.values() for x in l]; print("classes",len(cl),flush=True)
out=[]
for G,(n,W) in cl:
    c,x=cmin(G,rest); ns=[m for m in (13,14,19) if any(m==nn for nn in [n])]
    out.append((c/7,c,G.number_of_edges(),n,W)); print("density %.5f c<=%.5f edges %d C_%d^4 W=%s"%out[-1],flush=True)
out.sort(reverse=True); print("TOP"); [print("density %.5f c<=%.5f edges %d C_%d^4 W=%s"%o) for o in out[:15]]
