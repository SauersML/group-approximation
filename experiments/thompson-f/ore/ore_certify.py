#!/usr/bin/env python3
"""Produce explicit common multiples a u = b v over F_2 for given pairs, degree k, letter bound N.

Usage: ore_certify.py SET PAIRS.json OUT.json
PAIRS.json: list of {"a": int, "b": int, "k": int, "N": int}.
"""
import itertools, json, sys
from ore_linalg import SETS, normalize


def certificate(S, a, b, k, N):
    V = list(itertools.combinations_with_replacement(range(N + 1), k))
    rows = {}

    def vec(elem, u):
        out = 0
        for si, s in enumerate(S):
            if elem >> si & 1:
                nf = normalize(s + u)
                r = rows.get(nf)
                if r is None:
                    r = rows[nf] = len(rows)
                out ^= 1 << r
        return out

    cols = [vec(a, u) for u in V] + [vec(b, u) for u in V]
    piv = {}
    for i, c in enumerate(cols):
        comb = 1 << i
        while c:
            h = c.bit_length() - 1
            p = piv.get(h)
            if p is None:
                piv[h] = (c, comb)
                break
            c ^= p[0]
            comb ^= p[1]
        if c == 0:
            n = len(V)
            u = [list(V[j]) for j in range(n) if comb >> j & 1]
            v = [list(V[j - n]) for j in range(n, 2 * n) if comb >> j & 1]
            return u, v
    return None


if __name__ == "__main__":
    S = SETS[sys.argv[1]]
    with open(sys.argv[2]) as f:
        todo = json.load(f)
    out = []
    for t in todo:
        res = certificate(S, t["a"], t["b"], t["k"], t["N"])
        assert res is not None, t
        u, v = res
        out.append({"S": [list(s) for s in S], "a": t["a"], "b": t["b"], "k": t["k"],
                    "N": t["N"], "u": u, "v": v})
    with open(sys.argv[3], "w") as f:
        json.dump(out, f)
    print(json.dumps({"certificates": len(out)}))
