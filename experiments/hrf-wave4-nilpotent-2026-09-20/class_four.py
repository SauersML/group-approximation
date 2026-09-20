"""Exact marked low-class Lazard quotients over F7, in a tensor algebra.

The six generators are U0,V0,U1,V1,U2,V2. Lie polynomials are embedded
in the free associative algebra truncated above the requested degree. All row
operations are exact over F7; no external dependencies are used.
"""
from collections import deque
from pathlib import Path
import json
import argparse
import hashlib
import pickle
import time

P=7
parser=argparse.ArgumentParser()
parser.add_argument('--class-bound',type=int,choices=(2,3,4,5),default=4)
parser.add_argument('--checkpoint',type=Path)
parser.add_argument('--work-seconds',type=float,default=20)
args=parser.parse_args()
C=args.class_bound

def add(*terms):
    out={}
    for coefficient,term in terms:
        for word,value in term.items():
            out[word]=(out.get(word,0)+coefficient*value)%P
    return {w:v for w,v in out.items() if v}

def bracket(a,b):
    out={}
    for x,u in a.items():
        for y,v in b.items():
            if len(x)+len(y)>C: continue
            out[x+y]=(out.get(x+y,0)+u*v)%P
            out[y+x]=(out.get(y+x,0)-u*v)%P
    return {w:v for w,v in out.items() if v}

def product(a,b):
    out={}
    by_length={}
    for y,v in b.items():by_length.setdefault(len(y),[]).append((y,v))
    for x,u in a.items():
        for size in range(C-len(x)+1):
            for y,v in by_length.get(size,[]):
                out[x+y]=(out.get(x+y,0)+u*v)%P
    return {w:v for w,v in out.items() if v}

def exp_series(x):
    out={():1};term={():1};factorial=1
    for n in range(1,C+1):
        term=product(term,x);factorial=factorial*n%P
        out=add((1,out),(pow(factorial,-1,P),term))
    return out

def bch_series(x,y):
    h=add((1,product(exp_series(x),exp_series(y))),(-1,{():1}))
    out={};term={():1}
    for n in range(1,C+1):
        term=product(term,h)
        out=add((1,out),((1 if n%2 else -1)*pow(n,-1,P),term))
    return out

def bch_formula(x,y):
    xy=bracket(x,y)
    return add((1,x),(1,y),(pow(2,-1,P),xy),
               (pow(12,-1,P),bracket(x,xy)),
               (-pow(12,-1,P),bracket(y,xy)),
               (-pow(24,-1,P),bracket(y,bracket(x,xy))))

def bch(x,y):
    return bch_series(x,y) if C==5 else bch_formula(x,y)

gens=[{(i,):1} for i in range(6)]
if C<=4:
    assert bch_formula(gens[0],gens[1])==bch_series(gens[0],gens[1])

class Span:
    def __init__(self): self.rows={}
    def reduce(self,v):
        v=v.copy()
        # Every pivot row has no term below its pivot. Processing pivots
        # once in order therefore gives a full remainder without repeated
        # scans of all tensor monomials or copies of a large polynomial.
        for pivot in sorted(self.rows,key=lambda w:(len(w),w)):
            coefficient=v.get(pivot,0)
            if not coefficient:continue
            for word,value in self.rows[pivot].items():
                new=(v.get(word,0)-coefficient*value)%P
                if new:v[word]=new
                else:v.pop(word,None)
        return v
    def insert(self,v):
        v=self.reduce(v)
        if not v:return None
        pivot=min(v,key=lambda w:(len(w),w))
        v=add((pow(v[pivot],-1,P),v))
        self.rows[pivot]=v
        return v

def lie_closure(seeds,progress=False,checkpoint=None):
    span=Span();queue=deque()
    signature=hashlib.sha256(repr((C,seeds)).encode()).hexdigest()
    if checkpoint is not None and checkpoint.exists():
        saved=pickle.loads(checkpoint.read_bytes())
        assert saved['signature']==signature
        span.rows=saved['rows'];queue=deque(saved['queue'])
        print('resumed rank',len(span.rows),'pending',len(queue),flush=True)
    else:
        for seed in seeds:
            row=span.insert(seed)
            if row is not None:queue.append(row)
    started=time.monotonic()
    while queue:
        row=queue.popleft()
        if min(map(len,row))==C:
            continue
        for gen in gens:
            new=span.insert(bracket(row,gen))
            if new is not None:
                queue.append(new)
                if progress and len(span.rows)%200==0:
                    print('ideal rank',len(span.rows),flush=True)
        if checkpoint is not None and time.monotonic()-started>=args.work_seconds:
            checkpoint.write_bytes(pickle.dumps({'signature':signature,'rows':span.rows,'queue':list(queue)}))
            print('checkpoint rank',len(span.rows),'pending',len(queue),flush=True)
            return None
    if checkpoint is not None:
        checkpoint.write_bytes(pickle.dumps({'signature':signature,'rows':span.rows,'queue':[]}))
    return span

vertex_relations=[bracket(gens[0],gens[1])]
for j in (1,2):
    u,v=gens[2*j:2*j+2]
    w=bracket(u,v)
    vertex_relations.extend((bracket(u,w),bracket(v,w)))

def corner(j,i):
    u,v=gens[2*j:2*j+2]
    sign=(0,-1,1)[j]
    return add((i,u),(-i*i*pow(2,-1,P),v),
               (sign*i**3*pow(12,-1,P),bracket(u,v)))

def face(i):return bch(bch(corner(0,i),corner(1,i)),corner(2,i))

faces=[face(i) for i in range(7)]
print('face logarithms constructed',flush=True)
assert faces[0]=={}
mark=add((-1,faces[1]))
relations=vertex_relations+[add((1,r),(-1,faces[1])) for r in faces[2:]]
relations += [bracket(mark,g) for g in gens]
ambient_dimension=sum((6,15,70,315,1554)[:C])
if C<=4:
    ambient=lie_closure(gens)
    assert len(ambient.rows)==ambient_dimension
    assert all(not ambient.reduce(r) for r in relations)
# In class five the free-Lie dimension is the Witt formula. Every seed
# is a Lie polynomial by BCH; tensor injectivity does not require a
# redundant enumeration of the entire ambient basis.
ideal=lie_closure(relations,progress=True,checkpoint=args.checkpoint)
if ideal is None:raise SystemExit(0)
assert all(not ideal.reduce(bracket(row,g))
           for row in ideal.rows.values() if min(map(len,row))<C for g in gens)
assert all(not ideal.reduce(r) for r in relations)
remainder=ideal.reduce(mark)
result={'field':P,'nilpotency_class_bound':C,
        'ambient_free_lie_dimension':ambient_dimension,
        'ambient_dimension_check':'enumerated and Witt' if C<=4 else 'Witt formula',
        'ideal_dimension':len(ideal.rows),
        'quotient_dimension':ambient_dimension-len(ideal.rows),
        'mark_survives':bool(remainder),
        'mark_remainder':{' '.join(map(str,w)):v for w,v in remainder.items()},
        'interpretation':'Specified marked presentation only; no universal finite-quotient assertion.'}
Path(__file__).with_name({2:'class_two.json',3:'class_three.json',4:'class_four.json',5:'class_five.json'}[C]).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
