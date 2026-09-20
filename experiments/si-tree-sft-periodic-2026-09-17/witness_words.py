"""For random nonempty threshold pairs, record the reduced cyclic word along which
reachable sets never fill the alphabet (the SI-breaking witness). a/A = a^{+1}/a^{-1}, b/B likewise."""
import collections
import random
import sys
from treesft import essential, is_si, threshold_pair

L = "aAbB"


def cyc_word(Ra, Rb, n, E):
    ok, wit = is_si(Ra, Rb, n, E, return_witness=True)
    assert not ok
    s0, path, st = wit
    i = path.index(st)
    cyc = path[i + 1:] + [st]
    return "".join(L[x] for _, x in cyc)


def canon(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


n = int(sys.argv[1])
trials = int(sys.argv[2])
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 5)
cnt = collections.Counter()
for _ in range(trials):
    w = [rng.gauss(0, 1) for _ in range(n)]
    phi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    psi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    Ra, Rb = threshold_pair(w, phi, psi)
    E = essential(Ra, Rb, n)
    if E == 0:
        continue
    cnt[canon(cyc_word(Ra, Rb, n, E))] += 1
print(cnt.most_common(25))
