import re, itertools, networkx as nx
from cover import web
reps=[]
for l in sorted(set(x for x in open('cover7.log') if x.startswith('density'))):
    m=re.match(r"density (\S+) c<=(\S+) edges (\d+) C_(\d+)\^4 W=\((.*)\)",l)
    d,c,e,n=float(m[1]),float(m[2]),int(m[3]),int(m[4]); W=tuple(int(v) for v in m[5].split(','))
    E=web(n); G=nx.Graph(); G.add_nodes_from(range(7)); G.add_edges_from((a,b) for a in range(7) for b in range(a+1,7) if (W[a],W[b]) in E)
    reps.append((d,c,e,n,W,G))
for n in (13,14,19):
    E=web(n); found=set()
    for r in itertools.combinations(range(1,n),6):
        W=(0,)+r; G=nx.Graph(); G.add_nodes_from(range(7)); G.add_edges_from((a,b) for a in range(7) for b in range(a+1,7) if (W[a],W[b]) in E)
        if G.number_of_edges()<13: continue
        for i,R in enumerate(reps):
            if i not in found and R[2]==G.number_of_edges() and nx.is_isomorphic(G,R[5]): found.add((i)); reps[i]=R+(); break
    top=sorted((reps[i] for i in found),key=lambda r:-r[0])  # all classes present in C_n^4
    print("n",n,"classes",len(found)); [print("   %.5f c<=%.4f edges %d free %d  W=%s(C_%d)"%(r[0],r[1],r[2],r[2]-6,r[4],r[3])) for r in top]
