"""Count images s*w (s in S, w in M_(D,L)) shared by words w with different last letters.

0 means the last-letter fibration of research/thompson-f-monomial-doubling-width-bounds-degree-proof.md
is disjoint in degree D (proved for D >= L); nonzero values show where the proof stops.
usage: python3 last_letter_fibres.py "0,0;0,1;0,2;0,3;1,1;1,2;1,3;2,2;2,3" D L
Observed: X_2 and S_(3,5) give 0 at (D, L) = (5,5), (6,6), (7,7), (7,5) and nonzero at (5,6), (6,7).
"""
import itertools, sys
from collections import defaultdict

def lm(j, w):
    out = []
    k = 0
    n = len(w)
    while k < n and w[k] < j:
        out.append(w[k]); j += 1; k += 1
    out.append(j)
    out.extend(w[k:])
    return tuple(out)

def mul(a, w):
    for j in reversed(a):
        w = lm(j, w)
    return w

S = [tuple(map(int, s.split(','))) for s in sys.argv[1].split(';')]
D = int(sys.argv[2]); L = int(sys.argv[3])
img = defaultdict(set)
for w in itertools.combinations_with_replacement(range(L + 1), D):
    for s in S:
        img[mul(s, w)].add(w)
cross = 0
examples = []
for z, ws in img.items():
    lasts = {w[-1] for w in ws}
    if len(lasts) > 1:
        cross += 1
        if len(examples) < 5:
            examples.append((z, sorted(ws)))
print('D', D, 'L', L, 'images', len(img), 'cross-last-letter images', cross)
for e in examples:
    print(e)
