#!/usr/bin/env python3
"""Finite or infinite ray-loop subgroup H = <S, T> for each of the 472 linear bouquets.

finite : exact enumeration (closure under right multiplication by S, T; elements identified by
         level-4 fingerprints plus the exact triviality test), giving |H|;
infinite: an infinite-order certificate (power-section graph, as in same_point_screen.py) for
         a word in S, T.
Run: nice -n 10 timeout 3000 python3 h_finite.py > h_finite.out
"""
import itertools, sys
from bouquets import bouquets
from loopgraph import reduce, inv, fmt
from same_point_screen import infinite_order
from nucleus import Elements

def words_ST(I, maxlen):
    S, T = I["S"], I["T"]
    gens = {"S": S, "s": inv(S), "T": T, "t": inv(T)}
    for n in range(1, maxlen + 1):
        for w in itertools.product("SsTt", repeat=n):
            if any(a.lower() == b.lower() and a != b for a, b in zip(w, w[1:] + w[:1])): continue
            yield "".join(w), reduce(sum((gens[c] for c in w), ()))

def enumerate_H(R, I, cap):
    E = Elements(R, L=4, cap=10 ** 7)
    one = E.ident(()); seen, todo = {one}, [one]
    while todo:
        h = todo.pop()
        for g in (I["S"], I["T"]):
            k = E.ident(E.words[h] + g)
            if k not in seen:
                seen.add(k); todo.append(k)
                if len(seen) > cap: return None
    return len(seen)

def decide(R, I, cap=3000, maxlen=4):
    for label, w in words_ST(I, maxlen):
        c = infinite_order(R, w)
        if c: return "infinite", f"ord({label}) = inf, certificate {c}"
    if cap:
        n = enumerate_H(R, I, cap)
        if n: return "finite", n
    return "undecided", f"|H| > {cap}, no infinite-order word of length <= {maxlen}"

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
if __name__ == "__main__":
    tally = {}
    for k, (name, R, I) in enumerate(bouquets()):
        v, info = decide(R, I, cap=CAP)
        key = (v, info if v == "finite" else "")
        tally[key] = tally.get(key, 0) + 1
        print(k, name, "|", v, info, flush=True)
    print("\nverdict, |H| : count")
    for key, n in sorted(tally.items(), key=lambda kv: -kv[1]): print(" ", key, ":", n)
