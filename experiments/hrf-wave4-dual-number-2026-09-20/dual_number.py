"""Exact F7 certificates for scalar CCKW dual-number images; no dependencies."""
from itertools import product, combinations
from pathlib import Path
import json

P = 7

def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]

def zero(n,m=None):
    return [[0]*(n if m is None else m) for _ in range(n)]

def add(a,b):
    return [[(x+y)%P for x,y in zip(r,s)] for r,s in zip(a,b)]

def scale(a,n):
    return [[n*x%P for x in r] for r in a]

def mul(a,b):
    return [[sum(x*y for x,y in zip(r,c))%P for c in zip(*b)] for r in a]

def tr(a):
    return [list(c) for c in zip(*a)]

def power(a,n):
    out=eye(len(a))
    while n:
        if n&1: out=mul(out,a)
        a=mul(a,a);n//=2
    return out

def rref(a):
    a=[r[:] for r in a];piv=[];k=0
    for j in range(len(a[0]) if a else 0):
        i=next((i for i in range(k,len(a)) if a[i][j]%P),None)
        if i is None: continue
        a[k],a[i]=a[i],a[k]
        q=pow(a[k][j]%P,-1,P);a[k]=[x*q%P for x in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][j]:
                q=a[i][j];a[i]=[(x-q*y)%P for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
        if k==len(a): break
    return a[:k],piv

def inverse(a):
    n=len(a);r,p=rref([x+y for x,y in zip(a,eye(n))]);assert p[:n]==list(range(n))
    return [x[n:] for x in r]

def rank(a): return len(rref(a)[1])
def flatten(a): return sum(a,[])

I=eye(4)
A=eye(4);A[0][3]=A[1][2]=1
B=eye(4);B[1][0]=1;B[2][3]=6
C=eye(4);C[3][1]=1
gens=[A,B,C]
E=zero(4);E[3][1]=1
J=zero(4)
for i in range(2): J[i][i+2]=6;J[i+2][i]=1

basis=[]
for i,j in product(range(2),repeat=2):
    x=zero(4);x[i][j]=1;x[j+2][i+2]=6;basis.append(x)
for offset in (0,2):
    for i,j in ((0,0),(0,1),(1,1)):
        x=zero(4)
        if offset==0: x[i][j+2]=x[j][i+2]=1
        else: x[i+2][j]=x[j+2][i]=1
        basis.append(x)

def coords(x):
    assert add(mul(tr(x),J),mul(J,x))==zero(4)
    return [x[0][0],x[0][1],x[1][0],x[1][1],x[0][2],x[0][3],x[1][3],x[2][0],x[2][1],x[3][1]]

def adj(g):
    gi=inverse(g)
    return tr([coords(mul(mul(g,x),gi)) for x in basis])

ads=[adj(g) for g in gens]
assert all(mul(mul(tr(g),J),g)==J for g in gens)

def orbit_span(v,actors):
    rows=[v]
    while True:
        rows=rref(rows)[0]
        new=rref(rows+[[sum(a*b for a,b in zip(r,v))%P for r in g]
                       for g in actors for v in rows])[0]
        if len(new)==len(rows):return new
        rows=new

def matrix_word(w):
    out=I
    for s in w:out=mul(out,gens[s])
    return out

def order(g):
    h=I
    for n in range(1,401):
        h=mul(h,g)
        if h==I:return n
    raise ValueError('order exceeded search bound')

def cocycle_word(w):
    action=eye(10);f=zero(10,30)
    for s in w:
        for i in range(10):
            for j in range(10):f[i][10*s+j]=(f[i][10*s+j]+action[i][j])%P
        action=mul(action,ads[s])
    return action,f

def cocycle_power_relation(w,n):
    action,f=cocycle_word(w);total=zero(10);p=eye(10)
    for _ in range(n):total=add(total,p);p=mul(p,action)
    assert p==eye(10)
    return mul(total,f)

constraints=[];selected=[]
for length in range(1,7):
    for w in product(range(3),repeat=length):
        n=order(matrix_word(w));new=rref(constraints+cocycle_power_relation(w,n))[0]
        if len(new)>len(constraints):
            selected.append({'word':''.join('abc'[s] for s in w),'order':n,'rank':len(new)})
            constraints=new
        if len(constraints)==20:break
    if len(constraints)==20:break

coboundaries=[]
for g in ads:coboundaries+=add(g,scale(eye(10),-1))
gram=[[sum(mul(x,y)[i][i] for i in range(4))%P for y in basis] for x in basis]
assert rank(gram)==10

wedges=list(combinations(range(10),2))
def wedge(g):
    return [[(g[i][k]*g[j][l]-g[i][l]*g[j][k])%P for k,l in wedges] for i,j in wedges]

inv_vector_rank=rank(sum((add(g,scale(eye(10),-1)) for g in ads),[]))
inv_wedge_rank=rank(sum((add(wedge(g),scale(eye(45),-1)) for g in ads),[]))

def dual_mul(x,y):
    a,b=x;c,d=y
    return mul(a,c),add(mul(a,d),mul(b,c))

def dual_power(x,n):
    out=(I,zero(4))
    for _ in range(n):out=dual_mul(out,x)
    return out

dgens=[(A,zero(4)),(B,zero(4)),(C,E)]
kernel_word=None
for length in range(1,5):
    for w in product(range(3),repeat=length):
        d=(I,zero(4))
        for s in w:d=dual_mul(d,dgens[s])
        n=order(d[0]);p=dual_power(d,n)
        assert p[0]==I
        if p[1]!=zero(4):
            kernel_word={'word':''.join('abc'[s] for s in w),'power':n,'derivative_matrix':p[1],
                         'adjoint_orbit_rank':len(orbit_span(coords(p[1]),ads))}
            break
    if kernel_word:break

t_module=orbit_span(coords(E),ads[:2])
t_coinvariant_rank=rank(sum(([[(sum(g[i][j]*v[j] for j in range(10))-v[i])%P for i in range(10)] for v in t_module] for g in ads[:2]),[]))

assert len(constraints)==20
assert rank(coboundaries)==10
assert inv_vector_rank==10 and inv_wedge_rank==45
assert kernel_word['adjoint_orbit_rank']==10
assert len(t_module)==10 and t_coinvariant_rank==9
assert all(g[9]==eye(10)[9] for g in ads[:2])

out={'prime':P,'generators':gens,'symplectic_form':J,'lie_basis':basis,
     'cocycle_relations':selected,'cocycle_constraint_rank':len(constraints),
     'coboundary_rank':rank(coboundaries),'trace_pairing_rank':rank(gram),
     'vector_invariance_constraint_rank':inv_vector_rank,
     'wedge2_invariance_constraint_rank':inv_wedge_rank,
     'one_plus_t_kernel_certificate':kernel_word,
     't_module_rank':len(t_module),'t_module_coinvariant_dimension':len(t_module)-t_coinvariant_rank,
     't_module_basis':t_module}
Path(__file__).with_name('dual_number.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['generators','symplectic_form','lie_basis','t_module_basis']},indent=2))
