"""Test simple removal rules on L_{n,r} = {x in Z^n : 0<|x|_1<=r, x > 0 anti-lex}.
Rule: single pass in a given order; dominator chosen from a given family; report failures."""
import itertools, sys
from collections import Counter

def pts(n, r):
    out = []
    for x in itertools.product(range(-r, r + 1), repeat=n):
        s = sum(map(abs, x))
        if 0 < s <= r:
            last = [v for v in x if v]
            if last[-1] > 0:
                out.append(x)
    return out

def d(a, b):
    return sum(abs(p - q) for p, q in zip(a, b))

def pos(x):
    last = [v for v in x if v]
    return bool(last) and last[-1] > 0

def run(n, r, order_key, dom_family, verbose=False):
    P = pts(n, r)
    alive = set(P)
    P.sort(key=order_key)
    fails = []
    stats = Counter()
    for x in P:
        if sum(map(abs, x)) == 1:
            continue
        nb = [z for z in alive if z != x and d(z, x) <= r]
        ok = None
        for w in dom_family(x):
            if w in alive and w != x and pos(w) and all(d(z, w) <= r for z in nb):
                ok = w
                break
        if ok is None:
            fails.append(x)
        else:
            alive.discard(x)
            stats[tuple(abs(a - b) for a, b in zip(x, ok)).count(1) if True else 0] += 1
    return fails, stats

def lam(x, S):
    return tuple((v - (1 if v > 0 else -1)) if (i in S and v) else v for i, v in enumerate(x))

def fam_lambda(x):
    supp = [i for i, v in enumerate(x) if v]
    for k in range(1, len(supp) + 1):
        for S in itertools.combinations(supp, k):
            yield lam(x, set(S))

if __name__ == "__main__":
    n, r = int(sys.argv[1]), int(sys.argv[2])
    keys = {
        "norm": lambda x: -sum(map(abs, x)),
        "norm,maxabs": lambda x: (-sum(map(abs, x)), -max(map(abs, x))),
        "norm,supp": lambda x: (-sum(map(abs, x)), sum(1 for v in x if v)),
        "norm,-supp": lambda x: (-sum(map(abs, x)), -sum(1 for v in x if v)),
    }
    for name, k in keys.items():
        f, st = run(n, r, k, fam_lambda)
        print(name, "fails", len(f), f[:6], dict(st))
