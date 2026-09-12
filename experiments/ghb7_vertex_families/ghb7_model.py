#!/usr/bin/env python3
# kh-cckw model tests for the SL4(F7) quotient of GHB(7) (CCKW Prop 7.15, k=1). Runs on MSI.
import itertools
p = 7; n = 4
def mul(A, B): return tuple(tuple(sum(A[i][t]*B[t][j] for t in range(n)) % p for j in range(n)) for i in range(n))
I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
def E(entries):
    M = [list(r) for r in I]
    for (r, c), v in entries.items(): M[r][c] = (M[r][c] + v) % p
    return tuple(tuple(r) for r in M)
Va = E({(0,3):1, (1,2):1}); Vb = E({(1,0):1, (2,3):-1}); Vc = E({(3,1):1})
Vai = E({(0,3):-1, (1,2):-1}); Vbi = E({(1,0):-1, (2,3):1}); Vci = E({(3,1):-1})
assert mul(Va, Vai) == I and mul(Vai, Va) == I and mul(Vb, Vbi) == I and mul(Vc, Vci) == I
def inv(A):
    # unipotent: A^(7^4) = I so A^-1 = A^(7^4 - 1)
    R = I; B = A; e = 7**4 - 1
    while e:
        if e & 1: R = mul(R, B)
        B = mul(B, B); e >>= 1
    return R
def pw(A, e):
    R = I
    for _ in range(e): R = mul(R, A)
    return R
def comm(x, y): return mul(mul(mul(inv(x), inv(y)), x), y)
def show(M): return [[v for v in r] for r in M]
# relators
rels = [pw(Va,7), pw(Vb,7), pw(Vc,7), comm(comm(Va,Vb),Va), comm(comm(Va,Vb),Vb), comm(comm(Vc,Vb),Vc),
        comm(comm(comm(Vc,Vb),Vb),Vc), comm(comm(comm(Vc,Vb),Vb),Vb), comm(comm(Vc,Va),Vc),
        comm(comm(comm(Vc,Va),Va),Vc), comm(comm(comm(Vc,Va),Va),Va)]
print("relators all I:", all(r == I for r in rels))
# U3 normal form
C = comm(Va, Vb); print("C=[a,b]:", show(C))
ok = True; mats3 = set()
for i, j, k in itertools.product(range(7), repeat=3):
    M = mul(mul(pw(Va,i), pw(Vb,j)), pw(C,k)); mats3.add(M)
    if not (M[0][3] == i and M[1][0] == j and M[1][3] == (-i*j - 2*k) % p): ok = False
print("U3 readout (0,3)=i,(1,0)=j,(1,3)=-ij-2k:", ok, "distinct:", len(mats3))
def nf4(x, y):
    D = comm(x, y); Ee = comm(D, y)
    print("D=[x,y]:", show(D), " E=[x,y,y]:", show(Ee))
    mats = {}
    for i, j, k, l in itertools.product(range(7), repeat=4):
        M = mul(mul(mul(pw(x,i), pw(y,j)), pw(D,k)), pw(Ee,l)); mats[(i,j,k,l)] = M
    print("distinct:", len(set(mats.values())))
    # which entries are nonconstant, print dependence on basis vectors
    for pos in itertools.product(range(4), repeat=2):
        vals = set(M[pos[0]][pos[1]] for M in mats.values())
        if len(vals) > 1:
            print(" entry", pos, "e_i:", [mats[t][pos[0]][pos[1]] for t in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]],
                  "(1,1,0,0):", mats[(1,1,0,0)][pos[0]][pos[1]], "(2,1,0,0):", mats[(2,1,0,0)][pos[0]][pos[1]], "(1,2,0,0):", mats[(1,2,0,0)][pos[0]][pos[1]])
    return mats
print("== <c,b>"); m_cb = nf4(Vc, Vb)
print("== <c,a>"); m_ca = nf4(Vc, Va)
# element orders of simple words
def order(M, cap=10**6):
    R = M; o = 1
    while R != I:
        R = mul(R, M); o += 1
        if o > cap: return None
    return o
for name, M in [("ac", mul(Va,Vc)), ("bc", mul(Vb,Vc)), ("ab", mul(Va,Vb)), ("abc", mul(mul(Va,Vb),Vc))]:
    print("order of", name, "=", order(M))
# intersections of vertex images
cl_ab = mats3; cl_cb = set(m_cb.values()); cl_ca = set(m_ca.values())
pb = {pw(Vb,e) for e in range(7)}; pa = {pw(Va,e) for e in range(7)}; pc = {pw(Vc,e) for e in range(7)}
print("ab∩cb == <b>:", (cl_ab & cl_cb) == pb, " ab∩ca == <a>:", (cl_ab & cl_ca) == pa, " cb∩ca == <c>:", (cl_cb & cl_ca) == pc)
# link girth: alternating relations x^i y^j (len 2), x^i y^j x^k y^l (len 4), len 6
def girth_ok(x, y, maxlen):
    X = [pw(x,e) for e in range(1,7)]; Y = [pw(y,e) for e in range(1,7)]
    for L in range(1, maxlen+1):
        for t in itertools.product(range(6), repeat=2*L):
            M = I
            for s in range(L): M = mul(mul(M, X[t[2*s]]), Y[t[2*s+1]])
            if M == I: return (False, L, t)
    return (True,)
print("link <a,b> no alternating relation of length 2,4:", girth_ok(Va, Vb, 2))
print("link <c,b> no alternating relation of length 2,4,6:", girth_ok(Vc, Vb, 3))
print("link <c,a> no alternating relation of length 2,4,6:", girth_ok(Vc, Va, 3))
