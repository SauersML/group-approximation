"""Two-step rigidity check: #{C : D(K, C) = K h1 K, D(C, Kt) = K h2 K}
for all targets t (|t| <= T, t outside K) and labels |h| <= M.
Lemma A of the artifact says this is bounded by an absolute constant.
Usage: two_step.py M T L1 L2
"""
import sys
from collections import Counter
from chains import k_elements, reduced_words, in_K, cls
from simple import R_s

M, T, L1, L2 = (int(x) for x in sys.argv[1:5])
K1, K2 = k_elements(L1), k_elements(L2)
labs = [w for m in range(1, M + 1) for w in reduced_words(m) if not in_K(w)]
tg, seen = [], set()
for m in range(1, T + 1):
    for t in reduced_words(m):
        if in_K(t) or cls(t) in seen:
            continue
        seen.add(cls(t)); tg.append(t)
hist, unstable, best = Counter(), 0, (0, None)
for t in tg:
    for h1 in labs:
        for h2 in labs:
            r1 = R_s([h1, h2], K1, target=t)
            r2 = R_s([h1, h2], K2, target=t)
            unstable += r1 != r2
            hist[r2] += 1
            if r2 > best[0]:
                best = (r2, (t, h1, h2))
print('M', M, 'T', T, 'L', L1, L2, 'targets', len(tg), 'labels', len(labs))
print('hist', dict(sorted(hist.items())), 'unstable', unstable)
print('max', best)
