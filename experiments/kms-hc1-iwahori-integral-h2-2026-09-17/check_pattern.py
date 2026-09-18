#!/usr/bin/env python3
"""Check every weight line of an h2z.py output against the pattern

  H_2(L_Z) = Z^6 (degree 3, one Z per weight)
           + Z/n at weight n*delta (n >= 2)
           + Z/3 at each weight n*delta + alpha_i - alpha_j (n >= 2, i != j)
           + Z/2 at the weights (1,2,2),(2,1,2),(2,2,1)
  and H_1(L_Z) = Z^3 in degree 1, zero elsewhere, torsion-free.

Weights are (c0,c1,c2) in simple-root coordinates, delta = (1,1,1).
n*delta + alpha_i - alpha_j are exactly the weights whose coordinates are
(n-1, n, n+1) up to permutation.

usage: check_pattern.py h2z90.out   (prints the number of weights checked and
                                     every line that violates the pattern)
"""
import re, ast, sys

pat = re.compile(r"deg\s+(\d+) wt (\(.*?\)): .*H1 free (\d+) tors (\[.*?\])\s+H2 free (\d+) tors (\[.*?\])")

def expected(k, w):
    """(H1 free, H2 free, H2 torsion list) predicted at weight w of degree k."""
    lo = min(w)
    d = sorted(x - lo for x in w)
    if k == 3 and d == [0, 1, 2]:
        return 0, 1, []                   # Serre weights (0,1,2) permuted
    if w[0] == w[1] == w[2]:
        return 0, 0, ([lo] if lo >= 2 else [])
    if d == [0, 1, 2]:
        return 0, 0, [3]
    if sorted(w) == [1, 2, 2]:
        return 0, 0, [2]
    return 0, 0, []

n = 0
bad = []
seen = set()
K = 0
for line in open(sys.argv[1]):
    if line.startswith("degree"):
        K = max(K, int(line.split()[1].rstrip(":")))
    m = pat.match(line)
    if not m:
        continue
    n += 1
    k = int(m[1]); w = ast.literal_eval(m[2])
    seen.add(w)
    got = (int(m[3]), int(m[5]), ast.literal_eval(m[6]))
    if ast.literal_eval(m[4]) or got != expected(k, w):
        bad.append(line.rstrip())
# completeness: every weight where the pattern predicts nonzero H_2 must be listed
import itertools
want = set(itertools.permutations((0, 1, 2)))
for m_ in range(2, K // 3 + 1):
    want.add((m_, m_, m_))
    want |= set(itertools.permutations((m_ - 1, m_, m_ + 1)))
want |= {(1, 2, 2), (2, 1, 2), (2, 2, 1)}
missing = sorted(want - seen)
print(f"max degree {K}; {n} weights with nonzero H_2 listed, {len(want)} predicted; "
      f"{len(bad)} anomalies, {len(missing)} predicted weights missing")
for w in missing:
    print("MISSING", w)
for b in bad:
    print("ANOMALY", b)
