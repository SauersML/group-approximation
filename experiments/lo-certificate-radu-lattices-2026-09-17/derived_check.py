"""Independent membership check: every word in a certificate lies in the commutator
subgroup of the group given by the relators, i.e. its exponent-sum vector in Z^gens
is an integer combination of the relator exponent-sum vectors.
usage: python3 derived_check.py GROUP CERTFILE"""
import sys
from fractions import Fraction
import bmw

def vec(word, gens):
    v = [0] * len(gens)
    for t in word.split():
        e = -1 if t.endswith("^-1") else 1
        v[gens.index(t.split("^")[0])] += e
    return v

def solve_int(M, v):
    # M: list of columns (relator vectors); returns True iff v in Z-span, for full-rank square M
    n = len(v)
    A = [[Fraction(M[j][i]) for j in range(n)] + [Fraction(v[i])] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    sol = [A[i][n] / A[i][i] for i in range(n)]
    return all(s.denominator == 1 for s in sol)

name, path = sys.argv[1], sys.argv[2]
rels = {"radu44": bmw.RADU_44}[name]
gens = ["a1", "a2", "b1", "b2"]
M = [vec(r, gens) for r in rels]
det_check = solve_int(M, [0, 0, 0, 0])
bad = n = 0
for line in open(path):
    if line.startswith("#") or not line.strip():
        continue
    for w in line.split(";"):
        n += 1
        if not solve_int(M, vec(w, gens)):
            bad += 1; print("NOT IN COMMUTATOR SUBGROUP:", w.strip())
# negative control: a1 a2^-1 b1 b1 has ab-image not in span
print("control a1 b2 in span:", solve_int(M, vec("a1 b2", gens)), "| relator r1 in span:", solve_int(M, vec(rels[0], gens)))
print("words checked:", n, "outside [G,G]:", bad)
print("ALL WORDS IN COMMUTATOR SUBGROUP" if bad == 0 else "MEMBERSHIP FAILED")
