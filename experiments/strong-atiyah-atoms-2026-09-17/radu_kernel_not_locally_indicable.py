# Free-group check: rewritten relators of N=ker(Lambda_R -> Z) are conjugates of r1^{+-1}, r2^{+-1}
def red(w):
    out=[]
    for x in w:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return out
def inv(w): return [-x for x in reversed(w)]
def pw(w,n): return (w*n) if n>=0 else inv(w)*(-n)
F1=[1]; F2=[2]
def cat(*ws):
    r=[]
    for w in ws: r+=w
    return red(r)
def cycred(w):
    w=red(w)
    while len(w)>1 and w[0]==-w[-1]: w=w[1:-1]
    return w
def rots(w): return [tuple(w[k:]+w[:k]) for k in range(len(w))]
r1=cat(F2,inv(F1),pw(F2,-2),pw(F1,2),pw(F2,2),inv(F1),inv(F2),F1)
r2=cat(F1,pw(F2,-2),inv(F1),F2,F1,inv(F2),inv(F1),pw(F2,2),F1)
cands={name:set(rots(cycred(r))) for name,r in [("r1",r1),("r1^-1",inv(r1)),("r2",r2),("r2^-1",inv(r2))]}
def a(i): return cat(pw(F2,i),F1,pw(F2,-i))
ai=lambda i: inv(a(i))
for k in range(1,6):
    w=cat(ai(k+1),a(k-1),a(k-1),ai(k+1),a(k))
    print("type1",k,[n for n,s in cands.items() if tuple(cycred(w)) in s])
for k in range(2,7):
    w=cat(a(k),ai(k-2),a(k-1),ai(k-2),a(k))
    print("type2",k,[n for n,s in cands.items() if tuple(cycred(w)) in s])
print("F2 exponent sums", sum(1 if x==2 else -1 if x==-2 else 0 for x in r1), sum(1 if x==2 else -1 if x==-2 else 0 for x in r2))
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form
from sympy import ZZ
print("H1 of window groups N_[0,j]:")
for j in range(2,8):
    rows=[]
    for k in range(1,j):   # a(k+1)^-2 a(k-1)^2 a(k)
        v=[0]*(j+1); v[k+1]-=2; v[k-1]+=2; v[k]+=1; rows.append(v)
    for k in range(2,j+1): # a(k)^2 a(k-2)^-2 a(k-1)
        v=[0]*(j+1); v[k]+=2; v[k-2]-=2; v[k-1]+=1; rows.append(v)
    M=Matrix(rows)
    print(j, smith_normal_form(M,domain=ZZ).diagonal() if M.shape[0]>=M.shape[1] else smith_normal_form(M,domain=ZZ), M.shape)
