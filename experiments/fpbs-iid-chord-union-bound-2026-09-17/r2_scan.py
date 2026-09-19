"""Scan R_1 and R_2 over all labels of word length <= M outside K."""
import sys
from collections import Counter
from chains import R, k_elements, reduced_words, in_K

M = int(sys.argv[1]) if len(sys.argv) > 1 else 3
Ls = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [8, 12]
labels = [w for n in range(1, M + 1) for w in reduced_words(n) if not in_K(w)]
print('labels', len(labels))
KLs = {L: k_elements(L) for L in Ls}
r1 = Counter(R([h], KLs[Ls[-1]]) for h in labels)
print('R_1 histogram', dict(r1))
best = {}
hist = Counter()
unstable = 0
for h1 in labels:
    for h2 in labels:
        vals = [R([h1, h2], KLs[L]) for L in Ls]
        if vals[-1] != vals[-2]:
            unstable += 1
        hist[vals[-1]] += 1
        if vals[-1] >= max(best.values(), default=0):
            best[(h1, h2)] = vals[-1]
print('R_2 histogram', dict(sorted(hist.items())))
print('unstable pairs', unstable)
top = sorted(best.items(), key=lambda t: -t[1])[:8]
print('top', top)
