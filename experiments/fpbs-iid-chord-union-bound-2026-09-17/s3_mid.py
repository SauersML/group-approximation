"""Does N_3 grow with the length of a K-syllable buried inside the middle label?

h_2 = u k v with u, v short (outside K) and k in K of length ell.  The detour
C_1 -> C_2 -> Kb may then run along the hull of K for about ell steps, so the
number of admissible C_1 could grow with ell.  For each ell we report the max
of N_3 over short h_1, h_3, u, v and a few k of length ell, at two truncations.
Usage: s3_mid.py ell_max L1 L2
"""
import sys, random
from chains import k_elements, in_K, red
from simple import R_s

ellmax, L1, L2 = (int(x) for x in sys.argv[1:4])
random.seed(3)
K1, K2 = k_elements(L1), k_elements(L2)
short = ['b', 'B', 'ab', 'Ab', 'bA', 'ba', 'Ba', 'BA', 'aB', 'AB']
short = [w for w in short if not in_K(w)]
for ell in range(1, ellmax + 1):
    ks = [k for k in K1 if len(k) == ell]
    ks = random.sample(ks, min(4, len(ks)))
    best, unstable = (0, None), 0
    for k in ks:
        for u in ['b', 'B']:
            for v in ['b', 'B']:
                h2 = red(u + k + v)
                if in_K(h2):
                    continue
                for h1 in ['b', 'B', 'Ab', 'aB']:
                    for h3 in ['b', 'B', 'bA', 'Ba']:
                        r1 = R_s([h1, h2, h3], K1)
                        r2 = R_s([h1, h2, h3], K2)
                        unstable += r1 != r2
                        if r2 > best[0]:
                            best = (r2, (h1, h2, h3))
    print('ell', ell, 'max N_3', best, 'unstable', unstable, flush=True)
