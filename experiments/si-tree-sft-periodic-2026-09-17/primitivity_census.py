"""Census over random threshold pairs: how often are R_a and R_b (restricted to the essential
alphabet) primitive, and how often does the pair pass SI along the four one-letter-type words
a^k, b^k, (ab)^k, (ab^-1)^k? SI needs all of these."""
import random
import sys
from treesft import essential, restrict, step, threshold_pair, transpose


def fills(E, mats, n, maxlen=200):
    """From each singleton in E, apply the periodic sequence of matrices; True if all fill E."""
    for s in range(n):
        if not E >> s & 1:
            continue
        S = 1 << s
        seen = set()
        i = 0
        while S != E:
            key = (S, i % len(mats))
            if key in seen:
                return False
            seen.add(key)
            S = step(S, mats[i % len(mats)])
            i += 1
    return True


n = int(sys.argv[1])
trials = int(sys.argv[2])
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
stats = dict(nonempty=0, a=0, b=0, ab=0, aB=0, all4=0)
for _ in range(trials):
    w = [rng.gauss(0, 1) for _ in range(n)]
    phi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    psi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    Ra, Rb = threshold_pair(w, phi, psi)
    E = essential(Ra, Rb, n)
    if E == 0:
        continue
    stats["nonempty"] += 1
    Ra, Rb = restrict(Ra, E, n), restrict(Rb, E, n)
    Ta, Tb = transpose(Ra, n), transpose(Rb, n)
    fa = fills(E, [Ra], n)
    fb = fills(E, [Rb], n)
    fab = fills(E, [Ra, Rb], n)
    faB = fills(E, [Ra, Tb], n)
    stats["a"] += fa
    stats["b"] += fb
    stats["ab"] += fab
    stats["aB"] += faB
    stats["all4"] += fa and fb and fab and faB
    stats["a&b"] = stats.get("a&b", 0) + (fa and fb)
print(n, stats)
