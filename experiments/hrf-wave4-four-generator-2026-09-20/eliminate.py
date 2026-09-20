"""Exact filtered elimination to four generators for the marked GHB7 cover.

Associative tensor exp/log computes BCH through class <7. Two face
differences solve U2,V2 uniquely by a filtration-contractive iteration.
The remaining ideal is then closed in free Lie on U0,V0,U1,V1.
"""
from collections import deque
from pathlib import Path
import argparse,json,pickle,time,hashlib

ap=argparse.ArgumentParser()
ap.add_argument('--class-bound',type=int,choices=(2,3,4,5,6),default=4)
ap.add_argument('--work-seconds',type=float,default=20)
ap.add_argument('--checkpoint',type=Path)
ap.add_argument('--export',type=Path,help='Export an explicit finite-dimensional quotient Lie algebra witness.')
args=ap.parse_args();C=args.class_bound;P=7

def add(*terms):
    out={}
    for coeff,term in terms:
        for w,v in term.items():
            n=(out.get(w,0)+coeff*v)%P
            if n:out[w]=n
            else:out.pop(w,None)
    return out

def product(a,b):
    out={};bl={}
    for w,v in b.items():bl.setdefault(len(w),[]).append((w,v))
    for w,v in a.items():
        for l in range(C-len(w)+1):
            for z,x in bl.get(l,[]):
                key=w+z;n=(out.get(key,0)+v*x)%P
                if n:out[key]=n
                else:out.pop(key,None)
    return out

def bracket(a,b):return add((1,product(a,b)),(-1,product(b,a)))
def exp_series(x):
    out={():1};power={():1};factorial=1
    for n in range(1,C+1):
        power=product(power,x);factorial=factorial*n%P
        out=add((1,out),(pow(factorial,-1,P),power))
    return out
def bch(x,y):
    h=add((1,product(exp_series(x),exp_series(y))),(-1,{():1}))
    out={};power={():1}
    for n in range(1,C+1):
        power=product(power,h)
        out=add((1,out),((1 if n%2 else -1)*pow(n,-1,P),power))
    return out

gens=[{(i,):1} for i in range(4)]
def corner(j,i,six):
    u,v=six[2*j:2*j+2]
    return add((i,u),(-i*i*pow(2,-1,P),v),
               ((0,-1,1)[j]*i**3*pow(12,-1,P),bracket(u,v)))
def face(i,six):return bch(bch(corner(0,i,six),corner(1,i,six)),corner(2,i,six))
def degree(x):return min(map(len,x)) if x else C+1

six=gens+[add((-1,gens[0]),(-1,gens[2])),add((-1,gens[1]),(-1,gens[3]))]
steps=[]
for k in range(1,C):
    r1,r2,r3=[face(i,six) for i in (1,2,3)]
    e=add((1,r2),(-1,r1));f=add((1,r3),(-1,r1))
    assert min(degree(e),degree(f))>=k+1
    steps.append({'iteration':k,'input_residual_min_degree':min(degree(e),degree(f))})
    u,v=six[4:]
    six=gens+[add((1,u),(-4,e),(3*pow(2,-1,P),f)),add((1,v),(-2,e),(1,f))]
    print('elimination iteration',k,'complete',flush=True)

faces=[face(i,six) for i in range(7)]
assert faces[0]=={} and faces[1]==faces[2]==faces[3]
mark=add((-1,faces[1]))
relations=[bracket(six[0],six[1])]
for j in (1,2):
    u,v=six[2*j:2*j+2];w=bracket(u,v)
    relations.extend((bracket(u,w),bracket(v,w)))
relations += [add((1,faces[i]),(-1,faces[1])) for i in (4,5,6)]
# Centrality on four free generators suffices for all Lie polynomials.
relations += [bracket(mark,g) for g in gens]
print('substituted relations built',flush=True)

class Span:
    def __init__(self):self.rows={};self.pivots=[]
    def reduce(self,v):
        v=v.copy()
        for pivot in self.pivots:
            coefficient=v.get(pivot,0)
            if not coefficient:continue
            for w,x in self.rows[pivot].items():
                n=(v.get(w,0)-coefficient*x)%P
                if n:v[w]=n
                else:v.pop(w,None)
        return v
    def insert(self,v):
        v=self.reduce(v)
        if not v:return None
        p=min(v,key=lambda w:(len(w),w));v=add((pow(v[p],-1,P),v))
        self.rows[p]=v;self.pivots=sorted(self.rows,key=lambda w:(len(w),w))
        return v

signature=hashlib.sha256(repr((C,relations)).encode()).hexdigest()
span=Span();queue=deque()
if args.checkpoint and args.checkpoint.exists():
    old=pickle.loads(args.checkpoint.read_bytes());assert old['signature']==signature
    span.rows=old['rows'];span.pivots=sorted(span.rows,key=lambda w:(len(w),w));queue=deque(old['queue'])
    print('resumed',len(span.rows),'rows and',len(queue),'pending',flush=True)
else:
    for r in relations:
        new=span.insert(r)
        if new is not None:queue.append(new)

started=time.monotonic()
def checkpoint():
    if args.checkpoint:
        args.checkpoint.write_bytes(pickle.dumps({'signature':signature,'rows':span.rows,'queue':list(queue)}))

while queue:
    row=queue.popleft()
    for g in gens:
        new=span.insert(bracket(row,g))
        if new is not None:
            queue.append(new)
            if len(span.rows)%100==0:print('ideal rank',len(span.rows),flush=True)
    if args.checkpoint and time.monotonic()-started>=args.work_seconds:
        checkpoint();print('checkpoint',len(span.rows),'rows',len(queue),'pending',flush=True)
        raise SystemExit(0)
checkpoint()
assert all(not span.reduce(r) for r in relations)
assert all(not span.reduce(bracket(row,g)) for row in span.rows.values() for g in gens)
remaining=span.reduce(mark)
ambient=sum((4,6,20,60,204,670)[:C])
result={'field':7,'class_bound':C,'free_generators':4,'ambient_witt_dimension':ambient,
        'elimination_steps':steps,'eliminated_face_equations_exact':True,
        'ideal_dimension':len(span.rows),'quotient_dimension':ambient-len(span.rows),
        'mark_survives':bool(remaining),'mark_remainder':{' '.join(map(str,w)):v for w,v in remaining.items()},
        'closure_checked':True,'interpretation':'Exact universal marked class-C F7 Lie quotient after proved filtered elimination.'}
path=Path(__file__).with_name('class_'+str(C)+'.json');path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

if args.export:
    free=Span();todo=deque()
    for g in gens:
        row=free.insert(g)
        if row is not None:todo.append(row)
    while todo:
        row=todo.popleft()
        for g in gens:
            new=free.insert(bracket(row,g))
            if new is not None:todo.append(new)
    assert len(free.rows)==ambient
    quotient=Span();basis=[];index={}
    for p in free.pivots:
        row=quotient.insert(span.reduce(free.rows[p]))
        if row is not None:
            lead=min(row,key=lambda w:(len(w),w));index[lead]=len(basis);basis.append(row)
    assert len(basis)==result['quotient_dimension']
    def coordinates(v):
        v=span.reduce(v);out=[0]*len(basis)
        for p in quotient.pivots:
            coeff=v.get(p,0)
            if coeff:
                out[index[p]]=coeff
                v=add((1,v),(-coeff,quotient.rows[p]))
        assert not v
        return out
    for i,b in enumerate(basis):assert coordinates(b)==[int(i==j) for j in range(len(basis))]
    constants=[]
    for i in range(len(basis)):
        for j in range(i+1,len(basis)):
            row=coordinates(bracket(basis[i],basis[j]))
            if any(row):constants.append({'i':i,'j':j,'value':row})
    export={'prime':7,'class_bound':C,'dimension':len(basis),
            'basis_pivot_words':[list(min(b,key=lambda w:(len(w),w))) for b in basis],
            'brackets':constants,
            'vertex_generators':{name:coordinates(g) for name,g in zip(('U0','V0','U1','V1','U2','V2'),six)},
            'mark':coordinates(mark),
            'convention':'Antisymmetry extends listed [basis_i,basis_j]; unlisted brackets are zero. All coefficients mod7.'}
    args.export.write_text(json.dumps(export,indent=2)+'\n')
    print('explicit Lie witness exported:',args.export,flush=True)
