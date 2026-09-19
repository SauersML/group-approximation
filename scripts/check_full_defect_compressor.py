"""Exact noncommutative checks over Z<s,t,a,b>/(ts-1); no numeric sampling."""
from collections import defaultdict

def clean(p): return {w:c for w,c in p.items() if c}
def add(*ps):
    q=defaultdict(int)
    for p in ps:
        for w,c in p.items(): q[w]+=c
    return clean(q)
def neg(p): return {w:-c for w,c in p.items()}
def mul(p,q):
    r=defaultdict(int)
    for u,c in p.items():
        for v,d in q.items():
            w=u+v
            while 'ts' in w: w=w.replace('ts','')
            r[w]+=c*d
    return clean(r)
z={}; one={'':1}; s={'s':1}; t={'t':1}; a={'a':1}
e=add(one,neg(mul(s,t)))
def eye(n): return [[one if i==j else z for j in range(n)] for i in range(n)]
def mm(A,B):
    return [[add(*(mul(A[i][k],B[k][j]) for k in range(len(B))))
             for j in range(len(B[0]))] for i in range(len(A))]
def prod(*As):
    ans=eye(len(As[0]))
    for A in As: ans=mm(ans,A)
    return ans
def E(i,j,p,n=4):
    A=eye(n); A[i][j]=p; return A
def comm(A,Ai,B,Bi): return prod(A,B,Ai,Bi)
def piece(i):
    return prod(E(3,i,add(t,neg(one))),E(i,3,one),
                E(3,i,add(s,neg(one))),E(i,3,neg(t)))
U=prod(piece(2),piece(1),piece(0))
ss=mul(s,s); tt=mul(t,t)
expected=[[s,z,z,e],[z,s,z,mul(e,t)],
          [z,z,s,mul(e,tt)],[z,z,z,mul(tt,t)]]
assert U==expected, 'elementary factorization'
V=[[t,z,z,z],[z,t,z,z],[z,z,t,z],
   [e,mul(s,e),mul(ss,e),mul(ss,s)]]
assert mm(U,V)==eye(4) and mm(V,U)==eye(4), 'inverse'
for i in range(3):
    for j in range(3):
        if i!=j:
            assert prod(U,E(i,j,a),V)==E(i,j,mul(mul(s,a),t)), 'compression'
# Uppercase letters are nine additional, independent noncommuting variables.
A=eye(4)
compressed=eye(4)
for i in range(3):
    for j in range(3):
        A[i][j]={chr(65+3*i+j):1}
        compressed[i][j]=add(e if i==j else z,mul(mul(s,A[i][j]),t))
assert prod(U,A,V)==compressed, 'compression of a generic 3-by-3 matrix'
c=comm(E(3,0,e),E(3,0,neg(e)),E(0,3,t),E(0,3,neg(t)))
ci=comm(E(0,3,t),E(0,3,neg(t)),E(3,0,e),E(3,0,neg(e)))
ce=eye(4); ce[3][3]=add(one,mul(e,t))
assert c==ce and mm(c,ci)==eye(4), 'centralizer element'
assert prod(U,c,V)==E(0,1,e), 'transported centralizer'
d=comm(prod(U,c,V),prod(U,ci,V),E(1,2,one),E(1,2,neg(one)))
assert d==E(0,2,e), 'defect'
b={'b':1}
first=comm(E(3,0,a),E(3,0,neg(a)),d,E(0,2,neg(e)))
assert first==E(3,2,mul(a,e))
second=comm(first,E(3,2,neg(mul(a,e))),E(2,1,b),E(2,1,neg(b)))
assert second==E(3,1,mul(mul(a,e),b)), 'ideal propagation'
print('PASS: factorization, both inverses, generic matrix and root compressions,')
print('centralizer word, transported centralizer, defect, and ideal propagation.')
