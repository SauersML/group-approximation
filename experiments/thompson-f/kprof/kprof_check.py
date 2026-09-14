#!/usr/bin/env python3
"""Independent full-rank cross-check of kprof.c for small degrees.

Uses the normal-form rewriting of experiments/thompson-f/ore/ore_linalg.py (bubble rewrite
x_j x_i -> x_i x_(j+1), i < j), not the insertion rule used by kprof.c, and plain F_2 elimination on
Python integers.  Prints one JSON line per (pair, k): kernel = 2|V| - rank([A | B]).

Usage: kprof_check.py SET KMAX NOFF mode a b [a b ...]
"""
import itertools, json, sys


def normalize(w):
    w = list(w)
    changed = True
    while changed:
        changed = False
        for t in range(len(w) - 1):
            if w[t] > w[t + 1]:
                j, i = w[t], w[t + 1]
                w[t], w[t + 1] = i, j + 1
                changed = True
    return tuple(w)


def guba_set(m, d):
    out = []
    for w in itertools.combinations_with_replacement(range(m + d), d):
        if all(w[t] <= m + t for t in range(d)):
            out.append(w)
    return out


SETS = {"X2": guba_set(2, 1), "S24": guba_set(1, 2), "S35": guba_set(2, 2)}


def rank_f2(vectors):
    piv = {}
    r = 0
    for v in vectors:
        while v:
            h = v.bit_length() - 1
            p = piv.get(h)
            if p is None:
                piv[h] = v
                r += 1
                break
            v ^= p
    return r


def main():
    setname, kmax, noff, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    S = SETS[setname]
    pairs = [(int(sys.argv[i]), int(sys.argv[i + 1])) for i in range(5, len(sys.argv), 2)]
    for k in range(0, kmax + 1):
        N = k + noff
        if mode == "free":
            V = list(itertools.product(range(N + 1), repeat=k))
            nf = lambda w: tuple(w)
        else:
            V = list(itertools.combinations_with_replacement(range(N + 1), k))
            nf = normalize
        rows = {}
        img = []
        for s in S:
            col = []
            for u in V:
                key = nf(tuple(s) + tuple(u))
                r = rows.get(key)
                if r is None:
                    r = rows[key] = len(rows)
                col.append(1 << r)
            img.append(col)
        for a, b in pairs:
            vecs = []
            for m in (a, b):
                bits = [si for si in range(len(S)) if m >> si & 1]
                for ui in range(len(V)):
                    v = 0
                    for si in bits:
                        v ^= img[si][ui]
                    vecs.append(v)
            rk = rank_f2(vecs)
            print(json.dumps({"set": setname, "mode": mode, "k": k, "N": N, "a": a, "b": b,
                              "V": len(V), "rows": len(rows), "rank": rk, "kernel": 2 * len(V) - rk}),
                  flush=True)


if __name__ == "__main__":
    main()
