import networkx as nx
from fractions import Fraction
import itertools,json

def matrices(g):
 n=len(g); es=list(g.edges()); m=len(es)
 cnt=[[0]*n for _ in range(n)]; der=[[0]*n for _ in range(n)]
 for mask in range(1<<m):
  par=list(range(n))
  def root(i):
   while par[i]!=i:
    par[i]=par[par[i]];i=par[i]
   return i
  for j,(u,v) in enumerate(es):
   if (mask>>j)&1:par[root(u)]=root(v)
  roots=[root(i) for i in range(n)]; score=2*mask.bit_count()-m
  for x in range(n):
   for y in range(x+1,n):
    if roots[x]==roots[y]: cnt[x][y]+=1;der[x][y]+=score
 N=[[Fraction(0) for _ in range(n)] for _ in range(n)]
 for x in range(n):
  for y in range(x+1,n):N[x][y]=N[y][x]=Fraction(der[x][y],cnt[x][y])
 return N,cnt,der

total=0
for g in nx.graph_atlas_g():
 if not 3<=len(g)<=7 or g.number_of_edges()>11 or not nx.is_connected(g):continue
 total+=1
 N,_,_=matrices(g)
 for x,y,z in itertools.permutations(range(len(g)),3):
  if N[x][z]>N[x][y]+N[y][z]:
   print(json.dumps({'tested':total,'edges':list(g.edges()),'triple':[x,y,z],'N_xz':str(N[x][z]),'N_xy':str(N[x][y]),'N_yz':str(N[y][z])}));raise SystemExit
print('No failure',total)
