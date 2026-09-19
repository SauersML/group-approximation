"""R_2 for long labels: random pairs, and pairs built to share cancellations.

For a chain K -h1-> x -h2-> Kb, the pair (h1, h2) with h2 = b k h1^-1 k'
(k, k' in K) always has a chain; we look for pairs with many chains.
"""
import random, sys
from chains import R, k_elements, reduced_words, in_K, red, inv

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
KL12 = k_elements(12)
KL16 = k_elements(16)


def rword(n):
    w = ''
    while len(w) < n:
        x = random.choice('aAbB')
        if w and w[-1] == {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}[x]:
            continue
        w += x
    return w


Kshort = [k for k in KL12 if len(k) <= 6]
out = []
for trial in range(60):
    n1 = random.choice([4, 6, 8, 10])
    h1 = rword(n1)
    if in_K(h1):
        continue
    k = random.choice(Kshort)
    kp = random.choice(Kshort)
    h2 = red('b' + k + inv(h1) + kp)   # guaranteed chain through x = K h1
    if in_K(h2) or len(h2) > 14:
        continue
    r12 = R([h1, h2], KL12)
    r16 = R([h1, h2], KL16)
    out.append((r16, r12, h1, h2))
out.sort(reverse=True)
for t in out[:12]:
    print(t)
print('max', max(t[0] for t in out), 'pairs', len(out))
