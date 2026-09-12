#!/usr/bin/env python3
# kh-cckw: model test of the parameter-level decide statements of Kazhdan/CCKWLinkGirthTyped.lean.
import itertools
p = 7
def mulAB(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]+s[1]*t[0]-s[0]*t[1]) % p)
def mulCB(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]-s[1]*t[0]) % p, (s[3]+t[3]+s[2]*t[1]-s[1]*(t[2]+t[0]*t[1])) % p)
def mulCA(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]-s[1]*t[0]) % p, (s[3]+t[3]-s[2]*t[1]+s[1]*(t[2]+t[0]*t[1])) % p)
nz = range(1, 7)
print("m=1 AB:", all(mulAB((0,j,0),(i,0,0)) != (0,0,0) for j in nz for i in nz))
print("m=1 CB:", all(mulCB((0,j,0,0),(i,0,0,0)) != (0,0,0,0) for j in nz for i in nz))
print("m=1 CA:", all(mulCA((0,j,0,0),(i,0,0,0)) != (0,0,0,0) for j in nz for i in nz))
def six(mul, j1, i1, j2, i2):
    j3 = (-(j1+j2)) % p; i3 = (-(i1+i2)) % p
    r = mul(mul(mul(mul(mul((0,j1,0,0),(i1,0,0,0)),(0,j2,0,0)),(i2,0,0,0)),(0,j3,0,0)),(i3,0,0,0))
    return j3 == 0 or i3 == 0 or r != (0,0,0,0)
print("m=3 reduced CB:", all(six(mulCB, *t) for t in itertools.product(nz, repeat=4)))
print("m=3 reduced CA:", all(six(mulCA, *t) for t in itertools.product(nz, repeat=4)))
# full 6-variable check (the reduction is valid: coordinates 1 and 2 of the product are the sums)
def sixfull(mul):
    for j1, i1, j2, i2, j3, i3 in itertools.product(nz, repeat=6):
        r = mul(mul(mul(mul(mul((0,j1,0,0),(i1,0,0,0)),(0,j2,0,0)),(i2,0,0,0)),(0,j3,0,0)),(i3,0,0,0))
        if r == (0,0,0,0): return False
        if r[0] != (i1+i2+i3) % p or r[1] != (j1+j2+j3) % p: return "coord mismatch"
    return True
print("m=3 full CB:", sixfull(mulCB), " CA:", sixfull(mulCA))
