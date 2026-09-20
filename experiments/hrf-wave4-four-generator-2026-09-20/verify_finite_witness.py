"""Verify the explicit finite detector without the quotient-construction code.

Checks Lie axioms, nilpotency, generation, and the six marked BCH faces.
No external dependencies, free-Lie quotient ranks, or checkpoints are used.
"""
from pathlib import Path
from itertools import combinations,product
import json

data=json.loads(Path(__file__).with_name('class_five_lie_witness.json').read_text())
p=data['prime'];n=data['dimension']
assert p==7 and n==28
zero=(0,)*n
units=[tuple(int(i==j) for j in range(n)) for i in range(n)]

def plus(*terms):
    return tuple(sum(c*v[i] for c,v in terms)%p for i in range(n))

table={}
for item in data['brackets']:
    i,j=item['i'],item['j'];v=tuple(item['value'])
    assert 0<=i<j<n and len(v)==n and all(0<=x<p for x in v)
    assert (i,j) not in table
    table[i,j]=v
    table[j,i]=plus((-1,v))

def bracket(x,y):
    out=[0]*n
    for i,a in enumerate(x):
        if not a:continue
        for j,b in enumerate(y):
            if not b:continue
            for k,c in enumerate(table.get((i,j),zero)):
                out[k]=(out[k]+a*b*c)%p
    return tuple(out)

# Alternation is built into the table. By trilinearity, all Jacobi tests
# reduce to distinct ordered basis triples; repeated-index cases cancel.
for i,j,k in combinations(range(n),3):
    x,y,z=units[i],units[j],units[k]
    assert plus((1,bracket(x,bracket(y,z))),
                (1,bracket(y,bracket(z,x))),
                (1,bracket(z,bracket(x,y))))==zero

def basis(vectors):
    rows={}
    for v in vectors:
        v=list(v)
        for pivot,row in sorted(rows.items()):
            c=v[pivot]
            if c:v=[(a-c*b)%p for a,b in zip(v,row)]
        pivot=next((i for i,a in enumerate(v) if a),None)
        if pivot is not None:
            inv=pow(v[pivot],-1,p)
            rows[pivot]=tuple(a*inv%p for a in v)
    return list(rows.values())

gamma=[units]
for _ in range(5):
    gamma.append(basis(bracket(x,y) for x in gamma[-1] for y in units))
assert gamma[4] and not gamma[5]

vertex={key:tuple(value) for key,value in data['vertex_generators'].items()}
assert set(vertex)=={f'{letter}{j}' for letter in ('U','V') for j in range(3)}
assert all(len(v)==n and all(0<=x<p for x in v) for v in vertex.values())
z=tuple(data['mark'])
assert len(z)==n and z!=zero and all(0<=x<p for x in z)
assert all(bracket(z,x)==zero for x in units)
assert len(basis(gamma[4]+[z]))==len(gamma[4])
assert bracket(vertex['U0'],vertex['V0'])==zero
for j in (1,2):
    u,v=vertex[f'U{j}'],vertex[f'V{j}'];w=bracket(u,v)
    assert bracket(u,w)==bracket(v,w)==zero

generated=basis(vertex.values())
while True:
    enlarged=basis(generated+[bracket(x,y) for x in generated for y in vertex.values()])
    if len(enlarged)==len(generated):break
    generated=enlarged
assert len(generated)==n

# Independently construct the two-symbol BCH polynomial from exp/log.
# Convert it to nested Lie brackets and verify that conversion as a free
# associative identity, rather than assuming a stored BCH coefficient list.
C=5
def poly_add(*terms):
    out={}
    for c,term in terms:
        for word,value in term.items():out[word]=(out.get(word,0)+c*value)%p
    return {w:v for w,v in out.items() if v}
def poly_mul(a,b):
    out={}
    for x,u in a.items():
        for y,v in b.items():
            if len(x+y)<=C:out[x+y]=(out.get(x+y,0)+u*v)%p
    return {w:v for w,v in out.items() if v}
def poly_bracket(a,b):return poly_add((1,poly_mul(a,b)),(-1,poly_mul(b,a)))
def exp_symbol(letter):
    out={():1};factorial=1
    for k in range(1,C+1):
        factorial=factorial*k%p;out[(letter,)*k]=pow(factorial,-1,p)
    return out
h=poly_add((1,poly_mul(exp_symbol(0),exp_symbol(1))),(-1,{():1}))
power={():1};log={}
for k in range(1,C+1):
    power=poly_mul(power,h)
    log=poly_add((1,log),((1 if k%2 else -1)*pow(k,-1,p),power))
lie_terms=[];expanded={}
for word,coefficient in log.items():
    nested={(word[0],):1}
    for letter in word[1:]:nested=poly_bracket(nested,{(letter,):1})
    scalar=coefficient*pow(len(word),-1,p)%p
    lie_terms.append((word,scalar))
    expanded=poly_add((1,expanded),(scalar,nested))
assert expanded==log
def bch(x,y):
    values=(x,y);out=zero
    for word,scalar in lie_terms:
        value=values[word[0]]
        for letter in word[1:]:value=bracket(value,values[letter])
        out=plus((1,out),(scalar,value))
    return out

def corner(j,i):
    u,v=vertex[f'U{j}'],vertex[f'V{j}']
    return plus((i,u),(-i*i*pow(2,-1,p),v),
                ((0,-1,1)[j]*i**3*pow(12,-1,p),bracket(u,v)))
for i in range(1,7):
    face=bch(bch(corner(0,i),corner(1,i)),corner(2,i))
    assert face==plus((-1,z))

result={'verified':True,'field':p,'dimension':n,
        'jacobi_distinct_basis_triples':len(list(combinations(range(n),3))),
        'lower_central_dimensions':[len(g) for g in gamma],
        'vertex_generated_dimension':len(generated),'marked_face_relations':6,
        'mark_nonzero_and_central':True,'group_order':p**n,'mark_order':p,
        'virtual_splitting_index':p**(n-1)}
Path(__file__).with_name('finite_witness_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
