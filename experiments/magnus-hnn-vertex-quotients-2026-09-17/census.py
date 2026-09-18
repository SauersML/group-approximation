#!/usr/bin/env python3
"""Census of two-generator one-relator groups <a,b | w>, |w| <= L, w cyclically reduced,
not a proper power, both letters present, up to rotation/inversion/relabelling.
Counts how many are certified in H by the retract-only rules (old) and with the
bs-quotient rule (new).  Usage: census.py L"""
import sys, itertools, time
from hierarchy_certify import certify, cred, canon, is_proper_power

L = int(sys.argv[1])
LIMIT = int(sys.argv[2]) if len(sys.argv) > 2 else 5
gens = [("a", 1), ("a", -1), ("b", 1), ("b", -1)]
seen = set()
stats = {}
open_examples = {}
memo_old, memo_new = {}, {}
t0 = time.time()


def words(n):
    def rec(w):
        if len(w) == n:
            if w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
                return
            yield tuple(w)
            return
        for g in gens:
            if w and w[-1][0] == g[0] and w[-1][1] == -g[1]:
                continue
            w.append(g)
            yield from rec(w)
            w.pop()
    yield from rec([])


for n in range(2, L + 1):
    for w in words(n):
        if len({a for a, _ in w}) < 2:
            continue
        k = canon(w)
        if k in seen:
            continue
        seen.add(k)
        if is_proper_power(k):
            continue
        o, why_o = certify(w, "old", memo=memo_old)
        nw, why_n = certify(w, "new", memo=memo_new)
        key = (n, o, nw)
        stats[key] = stats.get(key, 0) + 1
        if not nw:
            open_examples.setdefault(n, []).append((k, why_n))
        elif not o and n not in open_examples.get("newonly", {}):
            open_examples.setdefault("newonly", {})[n] = (k, why_n)

print("length old new count")
for n in range(2, L + 1):
    for o in (True, False):
        for nw in (True, False):
            c = stats.get((n, o, nw), 0)
            if c:
                print(n, o, nw, c)


def show(k):
    return " ".join(("ab"[a] if e == 1 else "AB"[a]) for a, e in k)


print("first new-only certificates:")
for n, (k, why) in sorted(open_examples.get("newonly", {}).items()):
    print(n, show(k), why)
print("uncertified (up to LIMIT per length):")
for n in range(2, L + 1):
    for k, why in open_examples.get(n, [])[:LIMIT]:
        print(n, show(k), why)
print("time %.1fs" % (time.time() - t0))
