#!/usr/bin/env python3
"""Finite verifier for the S3 packet used in the Leavitt group-algebra analysis.

Everything here is exact over F_2.  Group elements are represented by their
2x2 matrices in GL_2(F_2); group-algebra elements are bitsets of those six
matrices.  No Leavitt-algebra relation is used in any group-algebra product.
"""
from itertools import product

I  = (1,0,0,1)
u  = (1,1,0,1)
v  = (1,0,1,1)
w  = (0,1,1,0)
g  = (0,1,1,1)
g2 = (1,1,1,0)
NAMES = {I:'1', u:'u', v:'v', w:'w', g:'g', g2:'g2'}
ELTS = [I,u,v,w,g,g2]

def mm(A,B):
    a,b,c,d=A; e,f,h,k=B
    return ((a*e+b*h)&1,(a*f+b*k)&1,(c*e+d*h)&1,(c*f+d*k)&1)

def addm(A,B): return tuple((x^y) for x,y in zip(A,B))
ZERO=(0,0,0,0)
E11=(1,0,0,0); E12=(0,1,0,0); E21=(0,0,1,0); E22=(0,0,0,1)

def ga(*xs):
    out=frozenset()
    for x in xs:
        out = out.symmetric_difference({x})
    return out

def plus(a,b): return a.symmetric_difference(b)

def mul(a,b):
    out=frozenset()
    for x in a:
        for y in b:
            out=out.symmetric_difference({mm(x,y)})
    return out

def ev(a):
    z=ZERO
    for x in a: z=addm(z,x)
    return z

def aug(a): return len(a)&1

def pretty(a): return '+'.join(NAMES[x] for x in ELTS if x in a) or '0'

# Basic group packet
assert len(set(ELTS)) == 6
assert all(mm(x,I)==x and mm(I,x)==x for x in ELTS)
assert all(mm(x,y) in ELTS for x in ELTS for y in ELTS)
assert mm(u,u)==I and mm(v,v)==I and mm(w,w)==I
assert mm(u,v)==g and mm(g,g)==g2 and mm(g,g2)==I
assert mm(v,u)==g2

one=ga(I)
trans=ga(u,v,w)             # known kernel element k
E=ga(g,g2)                  # idempotent e, evaluation I, augmentation 0
Z=ga(I,g,g2)                # complementary idempotent z, evaluation 0, augmentation 1
assert mul(E,E)==E
assert mul(Z,Z)==Z
assert mul(E,Z)==frozenset() and mul(Z,E)==frozenset()
assert plus(E,Z)==one
assert ev(E)==I and aug(E)==0
assert ev(Z)==ZERO and aug(Z)==1
assert ev(trans)==ZERO and aug(trans)==1
assert mul(E,trans)==frozenset() and mul(trans,E)==frozenset()

# Explicit complete 2x2 matrix units in e F2[S3] e.
f11=ga(I,u,v,g)
f22=ga(I,u,v,g2)
f12=ga(v,g,g2,w)
f21=ga(u,g,g2,w)
F={(0,0):f11,(0,1):f12,(1,0):f21,(1,1):f22}
assert plus(f11,f22)==E
expected={(0,0):E11,(0,1):E12,(1,0):E21,(1,1):E22}
for ij,x in F.items():
    assert mul(E,x)==x and mul(x,E)==x
    assert ev(x)==expected[ij], (ij,pretty(x),ev(x),expected[ij])
    assert aug(x)==0
for i,j,k,l in product(range(2), repeat=4):
    lhs=mul(F[(i,j)],F[(k,l)])
    rhs=F[(i,l)] if j==k else frozenset()
    assert lhs==rhs, ((i,j,k,l),pretty(lhs),pretty(rhs))

# Count the corner exactly: all eae with a in F2[S3].
all_ga=[]
for mask in range(1<<6):
    a=frozenset(ELTS[i] for i in range(6) if (mask>>i)&1)
    all_ga.append(a)
corner={mul(mul(E,a),E) for a in all_ga}
assert len(corner)==16
# The 16 linear combinations of f_ij are all distinct and exhaust the corner.
span=set()
units=[f11,f12,f21,f22]
for mask in range(16):
    a=frozenset()
    for i,x in enumerate(units):
        if (mask>>i)&1: a=plus(a,x)
    span.add(a)
assert span==corner

print('PASS: GL_2(F_2) packet has six distinct elements and S3 relations.')
print('PASS: e=g+g^2 and z=1+g+g^2 are complementary idempotents.')
print('PASS: k=u+v+w evaluates to 0 and e*k=k*e=0.')
print('PASS: f_ij satisfy all 16 matrix-unit multiplication rules in F2[S3].')
print('PASS: evaluations are f11->E11, f12->E12, f21->E21, f22->E22.')
print('PASS: e F2[S3] e has 16 elements and equals span{f11,f12,f21,f22} ~= M2(F2).')
print('f11 =', pretty(f11))
print('f12 =', pretty(f12))
print('f21 =', pretty(f21))
print('f22 =', pretty(f22))

# A direct-product certificate for the recursive kernel idempotent.
# Think of the first S3 as the scalar copy delta(S3), and the second as the
# constant S3.  In F2[S3 x S3], q = (z in first factor)*(f11 in second).
def pg(a,b):
    out=frozenset()
    for x in a:
        for y in b:
            out=out.symmetric_difference({(x,y)})
    return out

def pmul(a,b):
    out=frozenset()
    for (x1,x2) in a:
        for (y1,y2) in b:
            out=out.symmetric_difference({(mm(x1,y1),mm(x2,y2))})
    return out

q = pg(Z, f11)
assert len(q)==12
assert pmul(q,q)==q
# q lies under the constant primitive corner f11.
Fconst=pg(one,f11)
assert pmul(Fconst,q)==q and pmul(q,Fconst)==q
print('PASS: q=z_scalar*f11_constant has exactly 12 terms and is a nonzero idempotent.')
print('      This is the finite direct-product certificate underlying lambda(z) in ker(pi_e).')

# Explicit inverse table for every group element used in q.
INV = {I:I, u:u, v:v, w:w, g:g2, g2:g}
q_support = [(a,h) for a in (I,g,g2) for h in (I,u,v,g)]
assert len(set(q_support)) == 12
for a,h in q_support:
    ainv, hinv = INV[a], INV[h]
    # First and second factors commute in the direct product; inverse is componentwise.
    assert (mm(a,ainv), mm(h,hinv)) == (I,I)
    assert (mm(ainv,a), mm(hinv,h)) == (I,I)
print('PASS: all 12 support elements of q are pairwise distinct and have explicit componentwise inverses.')
print('q support/inverses:')
for a,h in q_support:
    print(f'  ({NAMES[a]},{NAMES[h]})^-1 = ({NAMES[INV[a]]},{NAMES[INV[h]]})')
