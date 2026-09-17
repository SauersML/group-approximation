"""Usage: Q=q classify_q3.py presentations.json.  Merge PGL(3,q)-orbits of triangle presentations under reversal T -> T^rev = {(z,y,x)}
(Gamma_T ~= Gamma_{T^rev} via a_x -> a_x^-1).  T^rev is a triangle presentation for the plane
structure N^rev(y) = {x : y in lambda(x)}; we transport it to the standard plane by a plane
isomorphism found by backtracking, then compare PGL(3,3)-canonical forms."""
import json, itertools, sys
FILE = sys.argv[1]
src = open("enumerate_pg2.py").read().split("nv = 0")[0]   # reuse plane + PGL(3,q) construction (q from $Q)
exec(src)

def alltrip(T):
    return {t[i:] + t[:i] for t in T for i in range(3)}
def canon(T):
    return min(tuple(sorted(cls((g[a], g[b], g[c])) for (a, b, c) in T)) for g in G)
def plane_iso(L1):
    """bijection s with s(line of L1) in standard lines"""
    L1 = [frozenset(l) for l in L1]; std = set(lines)
    s = {}
    def ok():
        for l in L1:
            im = {s[p] for p in l if p in s}
            if len(im) >= 2 and not any(im <= m for m in lines): return False
        return True
    def bt(p):
        if p == n: return True
        for v in range(n):
            if v in s.values(): continue
            s[p] = v
            if ok() and bt(p + 1): return True
            del s[p]
        return False
    assert bt(0)
    assert {frozenset(s[p] for p in l) for l in L1} == std
    return s
reps = json.load(open(FILE))
reps = [[tuple(t) for t in T] for T in reps]
can = [canon(T) for T in reps]
pair = {}
for i, T in enumerate(reps):
    A = alltrip(T)
    rev = {(z, y, x) for (x, y, z) in A}
    Nrev = [{x for (x, y, z) in A if y == yy} for yy in range(n)]
    s = plane_iso(Nrev)
    img = {cls((s[a], s[b], s[c])) for (a, b, c) in rev}
    pair[i] = can.index(canon(sorted(img)))
self_dual = [i for i in pair if pair[i] == i]
classes = {tuple(sorted((i, pair[i]))) for i in pair}
print("torsion-triple counts:", [sum(1 for t in T if len(set(t)) == 1) for T in reps])
print("PGL-orbits:", len(reps), " reversal-classes:", len(classes), " self-reversal orbits:", len(self_dual))
print("pairs:", sorted(classes))
