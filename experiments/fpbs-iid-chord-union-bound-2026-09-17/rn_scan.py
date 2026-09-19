"""Max and total of R_n over label sequences drawn from a finite label set.

S(n) = sum over signed label sequences from the set H^{+-} of R_n, divided by
|H^{+-}|^n, is the union-bound weight of n-step chains for the uniform
independent chord law on H.  We also report max R_n.
Usage: rn_scan.py M n L   (labels: reduced words of length <= M, outside K,
one per inverse pair).
"""
import sys, itertools
from chains import R_nb as R, k_elements, reduced_words, in_K, inv

M, n, L = (int(x) for x in sys.argv[1:4])
lab = []
seen = set()
for m in range(1, M + 1):
    for w in reduced_words(m):
        if in_K(w) or w in seen:
            continue
        seen.add(w); seen.add(inv(w))
        lab.append(w)
signed = lab + [inv(w) for w in lab]
KL = k_elements(L)
tot = 0
mx = (0, None)
for seq in itertools.product(signed, repeat=n):
    r = R(list(seq), KL)
    tot += r
    if r > mx[0]:
        mx = (r, seq)
print('M', M, 'n', n, 'L', L, 'labels', len(lab))
print('max R_n', mx)
print('mean R_n over signed sequences', tot / len(signed) ** n)
print('sum R_n', tot)
