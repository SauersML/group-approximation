#!/usr/bin/env python3
"""Decoder prefilter: which forward tables carry a nontrivial Dec-solution?

For a forward table T (a rook-independent partition of S x M), a rule mu: A^M -> A has a
decoder nu with Dec(T) iff the relay tuple determines the demand p(1,1) on every
T-constant assignment p. Trivial rules mu = f o pi_1 (f a permutation) always pass.
A realized strict pair needs a nontrivial rule with Dec at its realized forward table,
so the word-problem oracle is only needed on tables listed here.

Input tables.jsonl (enum_tables.py). Output JSON lines {id, nontrivial: [mu codes]}
for tables with at least one nontrivial Dec-rule, plus a summary line on stdout.
"""
import itertools, json, sys
import numpy as np

def partition_of(t):
    ns, nm = t["ns"], t["nm"]
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    cells = [f"{s}|{m}" for s in S for m in M]
    word = {k: tuple(v) for k, v in t["fwd"].items()}
    parent = {c: c for c in cells}
    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c
    wmap = {}
    for c in cells:
        wmap.setdefault(word[c], []).append(c)
    for a, b in t["rels"]:
        parent[find(wmap[tuple(a)][0])] = find(wmap[tuple(b)][0])
    cls = {}
    for c in cells:
        cls.setdefault(find(c), len(cls))
    return S, M, {c: cls[find(c)] for c in cells}, len(cls)

def trivial_codes(q, nm):
    codes = set()
    for f in itertools.permutations(range(q)):
        mu = [f[(idx // q ** (nm - 1)) % q] for idx in range(q ** nm)]  # first coordinate = label 1
        codes.add(sum(v * q ** i for i, v in enumerate(mu)))
    return codes

def main(inp, out, q):
    triv = None
    n_tables = n_hit = 0
    with open(out, "w") as fh:
        for line in open(inp):
            t = json.loads(line)
            n_tables += 1
            ns, nm = t["ns"], t["nm"]
            if triv is None:
                triv = trivial_codes(q, nm)
            S, M, cls, cf = partition_of(t)
            P = np.array(list(itertools.product(range(q), repeat=cf)), dtype=np.int64)
            rows = np.zeros((P.shape[0], ns), dtype=np.int64)
            for si, s in enumerate(S):
                for m in M:
                    rows[:, si] = rows[:, si] * q + P[:, cls[f"{s}|{m}"]]
            demand = P[:, cls["1|1"]]
            powq_s = q ** ns
            hits = []
            for code in range(q ** (q ** nm)):
                if code in triv:
                    continue
                mu = np.array([(code // q ** i) % q for i in range(q ** nm)], dtype=np.int64)
                y = mu[rows]
                yc = np.zeros(P.shape[0], dtype=np.int64)
                for si in range(ns):
                    yc = yc * q + y[:, si]
                lo = np.full(powq_s, q, dtype=np.int64)
                hi = np.full(powq_s, -1, dtype=np.int64)
                np.minimum.at(lo, yc, demand)
                np.maximum.at(hi, yc, demand)
                r = hi >= 0
                if np.all(lo[r] == hi[r]):
                    hits.append(code)
            if hits:
                n_hit += 1
                fh.write(json.dumps({"id": t["id"], "nontrivial": hits}) + "\n")
    print(json.dumps({"input": inp, "q": q, "tables": n_tables, "with_nontrivial_dec": n_hit}))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 2)
