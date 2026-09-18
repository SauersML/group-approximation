"""Sanity check for research/inseparable-heisenberg-shift-group-poisons-its-center-proof.md.

Model H = V x Z/k with (v,s)(v',s') = (v+v', s+s'+theta(v,v')), theta(e_i,e_j)=beta(j-i) for i<j.
Checks associativity, the inverse formula and [e_0,e_n] = c^beta(n) on a finite sample B.
Run: python3 heisenberg_model_check.py   (prints ok)
"""
import random
random.seed(0)
k=5
B={2,3,7}
beta=lambda d: 1 if d in B else 0
def theta(v,w):
    return sum(v.get(i,0)*w.get(j,0)*beta(j-i) for i in v for j in w if i<j)%k
def add(v,w):
    r=dict(v)
    for j,x in w.items(): r[j]=r.get(j,0)+x
    return {i:x for i,x in r.items() if x}
def mul(x,y): return (add(x[0],y[0]),(x[1]+y[1]+theta(x[0],y[0]))%k)
def inv(x):
    v={i:-a for i,a in x[0].items()}
    return (v,(-x[1]+theta(x[0],x[0]))%k)
e=lambda i:({i:1},0)
# associativity test
def rnd(): return ({random.randint(-3,9):random.randint(-2,2) for _ in range(3)},random.randint(0,k-1))
for _ in range(200):
    x,y,z=rnd(),rnd(),rnd()
    a=mul(mul(x,y),z); b=mul(x,mul(y,z))
    assert add(a[0],{i:-t for i,t in b[0].items()})=={} and a[1]==b[1]
    assert mul(x,inv(x))[1]==0 and mul(x,inv(x))[0]=={}
def comm(x,y): return mul(mul(inv(x),inv(y)),mul(x,y))
for n in range(1,10):
    c=comm(e(0),e(n)); assert c[0]=={} and c[1]==beta(n), (n,c)
print("ok")
