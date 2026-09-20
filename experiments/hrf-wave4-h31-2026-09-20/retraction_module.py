"""Exact mod-five abelianization of the canonical H31 retraction kernel.

Uses its cyclic F5[PSL2(31)] module presentation. No floating point.
"""
import json
from pathlib import Path
from flint import nmod_mat

q=31
p=5
def canon(m):
    m=tuple(x%q for x in m)
    return min(m,tuple(-x%q for x in m))
def mul(m,n):
    a,b,c,d=m; e,f,g,h=n
    return canon((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
I=canon((1,0,0,1))
a=canon((8,14,4,11)); b=canon((23,0,14,27))
def power(g,n):
    out=I
    for _ in range(n): out=mul(out,g)
    return out
assert all((m[0]*m[3]-m[1]*m[2])%q==1 for m in [a,b])
assert power(a,5)==power(b,5)==I and a!=I and b!=I
G={I}; queue=[I]
for g in queue:
    for x in [a,b]:
        h=mul(g,x)
        if h not in G: G.add(h);queue.append(h)
assert len(G)==14880
G=sorted(G)
# Check all three mixed a,b presentation relators explicitly.
def word(letters):
    v=I
    for gen,ex in letters: v=mul(v,power(gen,ex%5))
    return v
assert word([(a,1),(b,1),(a,2),(b,1),(a,2),(b,1),(a,1),(b,-1),(a,1),(b,-1)])==I
assert word([(b,2),(a,1),(b,1),(a,-1),(b,1),(a,-1),(b,1),(a,1),(b,2),(a,1)])==I
assert power(word([(b,1),(a,1),(b,-1),(a,1),(b,1),(a,-1)]),2)==I
ap=[power(a,i) for i in range(5)]
coset={}; representatives=[]
for g in G:
    if g in coset: continue
    k=len(representatives); representatives.append(g)
    block={mul(g,x) for x in ap}
    assert len(block)==5 and not block.intersection(coset)
    for h in block: coset[h]=k
assert len(representatives)==2976
b2=power(b,2)
rows=[]
for g in G:
    row={}
    for x,co in [(g,1),(mul(g,b),-2),(mul(g,b2),1)]:
        j=coset[x]; row[j]=(row.get(j,0)+co)%p
    rows.append({j:v for j,v in row.items() if v})
assert all(sum(r.values())%p==0 for r in rows)
print('Enumerated14880relations2976generators',flush=True)
M=nmod_mat(len(rows),len(representatives),p)
for i,row in enumerate(rows):
    for j,v in row.items(): M[i,j]=v
rank=M.rank()
result={'field':p,'simple_vertex_order':len(G),'module_generators':len(representatives),
        'relation_rows':len(rows),'rank':rank,'module_dimension':len(representatives)-rank,
        'matrices':{'a':a,'b':b}}
Path(__file__).with_name('retraction_module_result.json').write_text(json.dumps(result,indent=2)+'\n')
Path(__file__).with_name('retraction_module_rows.json').write_text(json.dumps({'modulus':p,'cols':len(representatives),'rows':rows})+'\n')
print(json.dumps(result),flush=True)
