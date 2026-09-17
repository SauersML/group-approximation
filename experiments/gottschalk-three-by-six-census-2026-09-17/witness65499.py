#!/usr/bin/env python3
"""Separation witness for survivor 65499, the one table left CANDIDATE by every automatic pass.

After the logged Tietze moves, P(T) = <x2, x3, x7 | u x2 u x2 u, u x2^-1 u^-1 x2^-2> with u = x7 x3^-1.
The Nielsen change x7 -> u x3 makes x3 a free factor: P(T) = Z * K, K = <u, a | u a u a u, u a u^-1 = a^-2>.
In K: u a = a^-2 u and u^2 a u^-2 = a^4, so u a u a u = a^-2 u^2 a u = a^2 u^3, whence u^3 = a^-2. Conjugating
a^-2 = u^3 by u gives a^-2 = a^4, so a^6 = 1; conjugating a by u^3 = a^-2 gives a = a^-8, so a^9 = 1; hence a^3 = 1,
u a u^-1 = a, a = u^3 and u^9 = 1. Conversely u -> generator of Z/9, a -> u^3 satisfies both relators. So K = Z/9 and
P(T) = Z * Z/9, which is residually finite. The automatic passes missed it because the quotients they tried were
either infinite (powers of one remaining generator) or not separating (Sims1 up to degree 10).

Search: u = a 9-cycle plus random fixed structure, x3 random, x2 = u^3, x7 = u x3 (as permutations acting on the
right, first letter first, as in verify.py). The original generators are the Tietze substitution words. The record
becomes RESOLVED when every relator of P(T) holds and the 18 reverse cells get 18 distinct permutations. verify.py
re-checks both facts from scratch, so nothing in the derivation above is trusted.

Usage: witness65499.py sc.jsonl latest_pass.jsonl out.jsonl [degree seed trials]
"""
import json
import random
import sys

ID = 65499


def mul(p, q):  # first p, then q
    return [q[x] for x in p]


def inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return r


def word(img, w, n):
    r = list(range(n))
    for x in w:
        r = mul(r, img[x] if x > 0 else inv(img[-x]))
    return r


def main():
    fsc, flatest, fout = sys.argv[1:4]
    deg = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    trials = int(sys.argv[6]) if len(sys.argv) > 6 else 20000
    ns, nm = 3, 6
    t = [json.loads(l) for l in open(fsc) if json.loads(l)["id"] == ID][0]["tietze"]
    rec = [json.loads(l) for l in open(flatest) if json.loads(l)["id"] == ID][0]
    rng = random.Random(seed)
    for trial in range(trials):
        # u: a 9-cycle on a random 9-subset, fixing the rest
        pts = rng.sample(range(deg), 9)
        u = list(range(deg))
        for i in range(9):
            u[pts[i]] = pts[(i + 1) % 9]
        x3 = list(range(deg))
        rng.shuffle(x3)
        img = {3: x3, 2: word({1: u}, [1, 1, 1], deg), 7: mul(u, x3)}
        assert all(word(img, q, deg) == list(range(deg)) for q in t["relators"])
        gens = [word(img, t["defs"][str(k)], deg) for k in range(1, ns + nm - 1)]
        # original relators x_s x_m = x_s' x_m' (letters 2k -> generator k+1)
        if any(word({i + 1: g for i, g in enumerate(gens)}, [a // 2 + 1 for a in u_], deg) !=
               word({i + 1: g for i, g in enumerate(gens)}, [a // 2 + 1 for a in v_], deg) for (u_, v_) in rec["rels"]):
            continue
        cells = [([ns - 1 + m] if m else []) + ([s] if s else []) for m in range(nm) for s in range(ns)]
        cimg = {tuple(word({i + 1: g for i, g in enumerate(gens)}, c, deg)) for c in cells}
        if len(cimg) == len(rec["rev_classes"]):
            out = {k: v for k, v in rec.items() if k != "unseparated"}
            out["witnesses"] = rec.get("witnesses", []) + [{"degree": deg, "gens": gens,
                                                            "quotient": {"structure": "Z * Z/9", "trial": trial,
                                                                         "seed": seed}}]
            out["status"] = "RESOLVED"
            with open(fout, "w") as fh:
                fh.write(json.dumps(out) + "\n")
            print(ID, "RESOLVED degree", deg, "trial", trial)
            return
    print(ID, "no witness found")


if __name__ == "__main__":
    main()
