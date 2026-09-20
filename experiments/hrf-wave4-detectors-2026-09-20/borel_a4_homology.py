"""Exact mod5 homology sector of the specified square kernel, via Borel x A4.

Sparse elimination is capped before any dense allocation exceeding4million entries.
"""
import json
from pathlib import Path
from flint import nmod_mat

q=19; p=5
def can(m):
    m=tuple(x%q for x in m)
    return min(m,tuple(-x%q for x in m))
def mul(x,y):
    a,b,c,d=x; e,f,g,h=y
    return can((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
def inv(x):
    a,b,c,d=x; z=pow((a*d-b*c)%q,-1,q)
    return can((d*z,-b*z,-c*z,a*z))
I=can((1,0,0,1))
def generate(gs):
    seen={I}; todo=[I]
    for x in todo:
        for g in gs:
            y=mul(g,x)
            if y not in seen: seen.add(y); todo.append(y)
    return sorted(seen)

G=sorted({can((a,b,c,d)) for a in range(q) for b in range(q)
          for c in range(q) for d in range(q) if (a*d-b*c)%q==1})
assert len(G)==3420
i=can((0,1,-1,0)); j=can((1,6,6,-1)); k=mul(i,j)
# A Hurwitz unit (-1+i+j+ij)/2 has projective order3.
h=can(tuple((-I[t]+i[t]+j[t]+k[t])*pow(2,-1,q) for t in range(4)))
A=generate([i,j,h]); assert len(A)==12
labels={}; representatives=[]
for g in G:
    if g in labels: continue
    label=len(representatives); representatives.append(g)
    for a in A: labels[mul(g,a)]=label
assert len(representatives)==285 and len(labels)==3420
xs=[can(x) for x in [(2,11,16,3),(5,11,4,9),(6,15,12,8)]]
u=can((1,5,9,17)); y=mul(mul(inv(u),xs[2]),u)
def mobius(m,t):
    a,b,c,d=m
    if t==19: return a*pow(c,-1,q)%q if c else 19
    den=(c*t+d)%q
    return (a*t+b)*pow(den,-1,q)%q if den else 19
def permutation(a,b):
    left=[mobius(a,t) for t in range(20)]
    right=[labels[mul(b,g)] for g in representatives]
    return [left[t]*285+right[r] for t in range(20) for r in range(285)]
perms=[permutation(xs[0],xs[0]),permutation(xs[1],xs[1]),permutation(xs[2],y)]
def partition(gens):
    lab=[-1]*5700; blocks=[]
    for start in range(5700):
        if lab[start]>=0: continue
        lab[start]=len(blocks); todo=[start]
        for a in todo:
            for g in gens:
                b=g[a]
                if lab[b]<0: lab[b]=lab[start]; todo.append(b)
        blocks.append(todo)
    return lab,blocks
vs=[partition([perms[a],perms[b]]) for a,b in [(0,1),(0,2),(1,2)]]
es=[partition([g]) for g in perms]
assert all(len(b)==5 for _,blocks in es for b in blocks)
assert all(3420%len(b)==0 and (3420//len(b))%5 for _,blocks in vs for b in blocks)
vertex_offsets=[0,len(vs[0][1]),len(vs[0][1])+len(vs[1][1])]
nv=sum(len(blocks) for _,blocks in vs)
parent=list(range(nv))
def find(x):
    while parent[x]!=x:
        parent[x]=parent[parent[x]]; x=parent[x]
    return x
tree=set(); endpoints=[]
for e,(a,b) in enumerate([(0,1),(0,2),(1,2)]):
    for o,block in enumerate(es[e][1]):
        z=block[0]; va=vertex_offsets[a]+vs[a][0][z]; vb=vertex_offsets[b]+vs[b][0][z]
        assert all(vs[a][0][x]==vs[a][0][z] and vs[b][0][x]==vs[b][0][z] for x in block)
        row=e*1140+o; endpoints.append((va,vb))
        ra,rb=find(va),find(vb)
        if ra!=rb: parent[ra]=rb; tree.add(row)
assert len(tree)==nv-1
rowids=[r for r in range(3420) if r not in tree]
ri={r:i for i,r in enumerate(rowids)}
cols={c:{ri[r]:v%5 for r,v in [(es[0][0][c],1),(1140+es[1][0][c],-1),(2280+es[2][0][c],1)]
         if r not in tree} for c in range(5700)}
rows={r:set() for r in range(len(ri))}
for c,col in cols.items():
    for r in col: rows[r].add(c)
print('SETUP',json.dumps({'degree':5700,'vertices':nv,'vertex_orbits':[[len(b) for b in blocks] for _,blocks in vs],
                          'edges':3420,'tree_edges':len(tree),'a4_generators':[i,j,h]}),flush=True)
eliminated=0
while len(rows)>500:
    candidate=None; score=None
    for c,col in cols.items():
        for r,v in col.items():
            s=((len(col)-1)*(len(rows[r])-1),len(col)+len(rows[r]),r,c)
            if score is None or s<score: score=s; candidate=(r,c,v)
    if candidate is None: break
    r,c,v=candidate; pivot=cols[c]; iv=pow(v,-1,5)
    for d in list(rows[r]):
        if d==c: continue
        col=cols[d]; factor=col[r]*iv%5
        for t,a in pivot.items():
            old=col.get(t,0); new=(old-factor*a)%5
            if new: col[t]=new; rows[t].add(d)
            elif old: del col[t]; rows[t].discard(d)
    for t in pivot: rows[t].discard(c)
    del cols[c]; del rows[r]; eliminated+=1
    cols={c:col for c,col in cols.items() if col}
    if eliminated%400==0:
        nnz=sum(map(len,cols.values()))
        print('ELIM',eliminated,'rows',len(rows),'cols',len(cols),'nnz',nnz,flush=True)
        if nnz>1000000: break
assert len(rows)*len(cols)<=4000000,'Dense allocation guard: report sparse partial result instead.'
rs=sorted(rows); cs=sorted(cols)
R=nmod_mat([[cols[c].get(r,0) for c in cs] for r in rs],5)
rr=R.rank(); rank=eliminated+rr
result={'field':19,'coefficient_prime':5,'cover_degree':5700,'vertices':nv,'edges':3420,'faces':5700,
        'sparse_pivots':eliminated,'residual_shape':[len(rs),len(cs)],'residual_rank':rr,
        'boundary_rank':rank,'h1_dimension':3420-(nv-1)-rank,
        'h2_dimension':5700-rank,'subgroup_order':171*12}
Path(__file__).with_name('borel_a4_homology_result.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',json.dumps(result),flush=True)
