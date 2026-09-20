"""Exact explicit PSL2(19) triangle and integral kernel abelianization.

Run with python-flint installed; no floating point arithmetic is used.
"""
import json
import random
from collections import deque
from fractions import Fraction
from pathlib import Path

Q = 19

def canon(m):
    m = tuple(x % Q for x in m)
    return min(m, tuple(-x % Q for x in m))

def mul(x, y):
    a,b,c,d=x; e,f,g,h=y
    return canon((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))

def inv(x):
    a,b,c,d=x
    return canon((d,-b,-c,a))

I=canon((1,0,0,1))
G=sorted({canon((a,b,c,d)) for a in range(Q) for b in range(Q)
          for c in range(Q) for d in range(Q) if (a*d-b*c)%Q==1})
assert len(G)==3420
idx={g:i for i,g in enumerate(G)}

def powers(x):
    out=[I]; y=x
    while y!=I:
        out.append(y); y=mul(y,x)
    return out

def generated(xs):
    seen={I}; todo=[I]; steps=xs+[inv(x) for x in xs]
    for g in todo:
        for x in steps:
            y=mul(x,g)
            if y not in seen:
                seen.add(y); todo.append(y)
    return seen

def cosets(x):
    cyc=powers(x); labels=[-1]*len(G); blocks=[]
    for j,g in enumerate(G):
        if labels[j]>=0: continue
        block=[idx[mul(y,g)] for y in cyc]
        for k in block: labels[k]=len(blocks)
        blocks.append(block)
    return labels,blocks

def girth(l1,l2):
    n=max(l1)+1; adj=[set() for _ in range(2*n)]
    for a,b in zip(l1,l2):
        adj[a].add(n+b); adj[n+b].add(a)
    assert all(len(v)==5 for v in adj)
    dist=[-1]*len(adj); parent=[-1]*len(adj); dist[0]=0
    todo=deque([0]); best=10**9
    while todo:
        a=todo.popleft()
        for b in sorted(adj[a]):
            if dist[b]<0:
                dist[b]=dist[a]+1; parent[b]=a; todo.append(b)
            elif parent[a]!=b:
                best=min(best,dist[a]+dist[b]+1)
    assert min(dist)>=0
    return best

rng=random.Random(20260920)
order5=[g for g in G if g!=I and len(powers(g))==5]
for trial in range(200):
    xs=rng.sample(order5,3)
    if any(len(generated([xs[i],xs[j]]))!=3420 for i,j in [(0,1),(0,2),(1,2)]):
        continue
    cs=[cosets(x) for x in xs]; ls=[c[0] for c in cs]
    gs=[girth(ls[i],ls[j]) for i,j in [(0,1),(0,2),(1,2)]]
    if sum(Fraction(2,g) for g in gs)<1:
        break
else:
    raise RuntimeError('No triangle found')

print('SEED',json.dumps({'trial':trial,'matrices':xs,'girths':gs}),flush=True)
assert all(len(c[1])==684 for c in cs)
# Collapse one edge of types 0 and 1, which form a spanning tree on the
# three quotient vertices. A face has signed boundary e0 - e1 + e2.
deleted={0,684}
rowids=[r for r in range(2052) if r not in deleted]
reindex={r:i for i,r in enumerate(rowids)}
cols={j:{reindex[r]:v for r,v in [(ls[0][j],1),(684+ls[1][j],-1),(1368+ls[2][j],1)]
         if r not in deleted} for j in range(3420)}
rows={i:set() for i in range(2050)}
for j,col in cols.items():
    for i in col: rows[i].add(j)
eliminated=0
while True:
    candidate=None; cost=None
    for j,col in cols.items():
        for i,v in col.items():
            if abs(v)!=1: continue
            score=((len(col)-1)*(len(rows[i])-1),len(col)+len(rows[i]),i,j)
            if cost is None or score<cost:
                candidate=(i,j,v); cost=score
    if candidate is None: break
    r,c,v=candidate; pivot=cols[c]
    for j in list(rows[r]):
        if j==c: continue
        col=cols[j]; factor=col[r]*v
        for i,a in pivot.items():
            old=col.get(i,0); new=old-factor*a
            if new:
                col[i]=new; rows[i].add(j)
            elif old:
                del col[i]; rows[i].discard(j)
    for i in pivot: rows[i].discard(c)
    del cols[c]; del rows[r]; eliminated+=1
    if eliminated%200==0:
        print('ELIM',eliminated,'rows',len(rows),'cols',len(cols),'nnz',sum(map(len,cols.values())),flush=True)
    # Exact empty-column deletion does not affect the image lattice.
    cols={j:col for j,col in cols.items() if col}

print('RESIDUAL',eliminated,len(rows),len(cols),sum(map(len,cols.values())),flush=True)
from flint import fmpz_mat
ri=sorted(rows); cj=sorted(cols)
A=fmpz_mat([[cols[j].get(i,0) for j in cj] for i in ri])
S=A.snf() if ri and cj else A
diagonal=[int(S[i,i]) for i in range(min(len(ri),len(cj)))]
nonzero=[abs(x) for x in diagonal if x]
torsion=[x for x in nonzero if x>1]
rank=eliminated+len(nonzero)
H=A.transpose().hnf() if ri and cj else A
assert len(ri)==len(nonzero) and not torsion
assert all(int(H[i,j])==int(i==j) for i in range(len(cj)) for j in range(len(ri)))
Path(__file__).with_name('psl19_residual.json').write_text(json.dumps({
    'rows':ri,'columns':cj,
    'matrix':[[int(A[i,j]) for j in range(len(cj))] for i in range(len(ri))]
})+'\n')
result={'field':Q,'prime':5,'group_order':3420,'trial':trial,'matrices':xs,
        'girths':gs,'vertices':3,'edges':2052,'faces':3420,
        'unit_eliminations':eliminated,'residual_rows':len(ri),'residual_columns':len(cj),
        'boundary_rank':rank,'h1_free_rank':2050-rank,'h1_torsion_invariants':torsion,
        'transpose_hnf_is_identity_above_zero':True}
Path(__file__).with_name('psl19_kernel_result.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',json.dumps(result),flush=True)
