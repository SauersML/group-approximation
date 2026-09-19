"""Cross-check mult.py's closed form against the syllable-by-syllable push of w13-053's pathstab.py."""
import sys, random
e = int(sys.argv[1]); sys.argv = [sys.argv[0], str(e), '1']
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'higman-b-splitting-2026-09-18'))  # w13-053 pathstab.py
from pathstab import push, red, inv, m
from mult import make
def left(s, word, j):
    w2, i2 = push(s, -j, inv(word)); return (-i2) % m, inv(w2)
def act(gword, vert):
    out = []; beta = gword
    for idx, x in enumerate(vert):
        s = 'a' if idx % 2 == 0 else 'c'
        x2, beta = left(s, beta, x); out.append(x2)
    return tuple(out)
_, T, bu, du, a = make(e)
random.seed(1); bad = 0
for trial in range(3000):
    L = random.randint(1, 9); x = tuple([random.randrange(m)] + [random.randrange(1, m) for _ in range(L - 1)])
    u = random.randrange(1, m)
    if act((('b', u),), x) != bu(u, x): bad += 1
    if act((('d', u),), x) != du(u, x): bad += 1
print('e=%d mismatches %d' % (e, bad))
