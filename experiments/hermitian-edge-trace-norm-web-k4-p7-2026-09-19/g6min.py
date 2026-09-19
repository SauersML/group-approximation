import sys, numpy as np, networkx as nx
from cover import cmin
G=nx.Graph(); G.add_nodes_from(range(6))
G.add_edges_from([(a,b) for a in range(5) for b in range(a+1,5)]+[(2,5),(3,5),(4,5)])
for seed in range(int(sys.argv[1])):
    c,x=cmin(G,10,seed=seed); print("seed",seed,"c<= %.6f"%c,flush=True)
    np.save("g6_best_%d.npy"%seed,x)
