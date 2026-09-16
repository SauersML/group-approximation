#!/usr/bin/env python3
"""Independent consistency check of classify.py.

For every table T, count |Hom(P(T), F)| by brute force over generator tuples of
the ORIGINAL presentation (no Tietze moves), and compare with the count predicted
by the claimed free-product decomposition, |Hom(*_i G_i, F)| = prod_i |Hom(G_i, F)|,
for several small finite groups F.  A mismatch refutes the classification of T.
"""
import itertools
import json
import sys

from tables import tables, gen_names


def perm_group(gens, limit=64):
    """Closure of a list of permutation tuples; returns (order, mul, inv).
    Aborts if the generated group has more than `limit` elements."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    seen = {ident: 0}
    frontier = [ident]
    while frontier:
        new = []
        for p in frontier:
            for g in gens:
                q = tuple(p[g[i]] for i in range(n))
                if q not in seen:
                    seen[q] = len(elems)
                    elems.append(q)
                    new.append(q)
                    if len(elems) > limit:
                        raise ValueError("generated group too large")
        frontier = new
    N = len(elems)
    mul = [[seen[tuple(elems[a][elems[b][i]] for i in range(n))] for b in range(N)]
           for a in range(N)]
    inv = [next(b for b in range(N) if mul[a][b] == 0) for a in range(N)]
    return N, mul, inv


def cyclic(n):
    return perm_group([tuple((i + 1) % n for i in range(n))])


# Q8 on the points (1, i, j, k, -1, -i, -j, -k) = (0..7): left multiplication by i, j.
GROUP_SPECS = {
    "C4": (4, lambda: cyclic(4)),
    "C6": (6, lambda: cyclic(6)),
    "C2xC2": (4, lambda: perm_group([(1, 0, 3, 2), (2, 3, 0, 1)])),
    "S3": (6, lambda: perm_group([(1, 0, 2), (1, 2, 0)])),
    "D4": (8, lambda: perm_group([(1, 2, 3, 0), (3, 2, 1, 0)])),
    "Q8": (8, lambda: perm_group([(1, 4, 3, 6, 5, 0, 7, 2), (2, 7, 4, 1, 6, 3, 0, 5)])),
    "C5": (5, lambda: cyclic(5)),
    "A4": (12, lambda: perm_group([(1, 2, 0, 3), (1, 0, 3, 2)])),
}


def get_group(name):
    order, build = GROUP_SPECS[name]
    G = build()
    assert G[0] == order, (name, G[0])
    return G


def is_abelian(G):
    N, mul, _ = G
    return all(mul[a][b] == mul[b][a] for a in range(N) for b in range(N))


def factor_count(name, G):
    N, mul, inv = G
    if name == "1":
        return 1
    if name == "Z":
        return N
    if name.startswith("F"):
        return N ** int(name[1:])
    if name.startswith("Z/") and "x" not in name:
        n = int(name[2:])
        cnt = 0
        for x in range(N):
            y = 0
            for _ in range(n):
                y = mul[y][x]
            cnt += (y == 0)
        return cnt
    pairs = itertools.product(range(N), repeat=2)
    if name == "ZxZ":
        return sum(1 for a, b in pairs if mul[a][b] == mul[b][a])
    if name == "Z/2xZ":
        return sum(1 for a, b in pairs if mul[a][b] == mul[b][a] and mul[a][a] == 0)
    if name == "Z/2xZ/2":
        return sum(1 for a, b in pairs
                   if mul[a][b] == mul[b][a] and mul[a][a] == 0 and mul[b][b] == 0)
    if name == "K(bab^-1=a^-1)":
        return sum(1 for a, b in pairs if mul[mul[b][a]][inv[b]] == inv[a])
    if name == "K(a^2=b^2)":
        return sum(1 for a, b in pairs if mul[a][a] == mul[b][b])
    raise ValueError(name)


def eval_word(w, assign, mul, inv):
    y = 0
    for x in w:
        g = assign[abs(x) - 1]
        y = mul[y][g if x > 0 else inv[g]]
    return y


def presentation_count(ngens, rels, G):
    N, mul, inv = G
    cnt = 0
    for assign in itertools.product(range(N), repeat=ngens):
        if all(eval_word(r, assign, mul, inv) == 0 for r in rels):
            cnt += 1
    return cnt


def main(classify_path, group_names):
    recs = {}
    for line in open(classify_path):
        r = json.loads(line)
        recs[(tuple(r["shape"]), r["id"])] = r
    groups = {g: get_group(g) for g in group_names}
    mismatches = 0
    checked = 0
    for shape in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        ng = len(gen_names(*shape))
        for tid, (part, rels) in enumerate(tables(*shape)):
            rec = recs[(shape, tid)]
            assert not rec["unknown"], (shape, tid)
            for gname in group_names:
                G = groups[gname]
                pred = 1
                for f in rec["factors"]:
                    pred *= factor_count(f, G)
                obs = presentation_count(ng, rels, G)
                checked += 1
                if pred != obs:
                    mismatches += 1
                    print("MISMATCH", shape, tid, gname, rec["factors"], pred, obs)
    print(f"checked {checked} (table, group) pairs over {group_names}: {mismatches} mismatches")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2].split(","))
