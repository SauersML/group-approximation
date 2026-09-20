"""Enumerate admissible eigenvalue types (alpha in mu_4, beta in mu_3) for Delta(4,3,5) in U(n).

det(A) det(B) = det(BA) lies in mu_4 mu_3 cap mu_5 = {1}, so sum(alpha) = 0 mod 4 and
sum(beta) = 0 mod 3.  Scalar A or B is dropped (it forces n = 1 for irreducibles).
Prints one line "alpha beta" per type.
"""
import sys
from itertools import combinations_with_replacement as cwr

n = int(sys.argv[1])
As = [c for c in cwr(range(4), n) if sum(c) % 4 == 0 and len(set(c)) > 1]
Bs = [c for c in cwr(range(3), n) if sum(c) % 3 == 0 and len(set(c)) > 1]
for a in As:
    for b in Bs:
        print(''.join(map(str, a)), ''.join(map(str, b)))
