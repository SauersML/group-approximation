#!/usr/bin/env python3
"""Independent control for flip1.py.

Over concrete finite groups (multiplication tables built from permutations), with random
four-element placements containing the identity, decide by direct evaluation whether a single
flip at the identity can be invisible: enumerate all assignments on the context set
S = {m_i^-1 m_j}, set x = 0 elsewhere, and compare tau(x) with tau(x') at EVERY group element.
Compare with flip1's verdict on the realized quotient partition.  Also check that every realized
partition appears in flip1's admissible list.
"""
import itertools, json, random, sys


def perm_group(gens):
    n = len(gens[0])
    ident = tuple(range(n))
    elems = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[i]] for i in range(n))  # q = g o p
                if q not in elems:
                    elems.add(q)
                    nxt.append(q)
        frontier = nxt
    elems = sorted(elems)
    idx = {e: k for k, e in enumerate(elems)}
    # product: (x * y)(i) = x(y(i))  (apply y first)
    mul = [[idx[tuple(x[y[i]] for i in range(n))] for y in elems] for x in elems]
    e = idx[ident]
    inv = [None] * len(elems)
    for a in range(len(elems)):
        for b in range(len(elems)):
            if mul[a][b] == e:
                inv[a] = b
    return mul, inv, e


def cyclic(n):
    return [tuple((i + 1) % n for i in range(n))]


def dihedral(n):
    return [tuple((i + 1) % n for i in range(n)), tuple((-i) % n for i in range(n))]


GROUPS = {
    "Z7": cyclic(7), "Z12": cyclic(12), "D5": dihedral(5), "D8": dihedral(8),
    "A4": [(1, 2, 0, 3), (0, 2, 3, 1)],
    "S4": [(1, 0, 2, 3), (1, 2, 3, 0)],
    "A5": [(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)],
    # left-regular representation of Q8 on (1, i, j, k, -1, -i, -j, -k)
    "Q8": [(1, 4, 3, 6, 5, 0, 7, 2), (2, 7, 4, 1, 6, 3, 0, 5)],
    "S3xS3": [(1, 0, 2, 3, 4, 5), (1, 2, 0, 3, 4, 5), (0, 1, 2, 4, 3, 5), (0, 1, 2, 4, 5, 3)],
}
EXPECTED_ORDERS = {"Z7": 7, "Z12": 12, "D5": 10, "D8": 16, "A4": 12, "S4": 24, "A5": 60,
                   "Q8": 8, "S3xS3": 36}

PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]


def rgs(labels):
    seen, out = {}, []
    for l in labels:
        if l not in seen:
            seen[l] = len(seen)
        out.append(seen[l])
    return tuple(out)


def rule_eval(mu, bits):
    x = bits[0] | (bits[1] << 1) | (bits[2] << 2) | (bits[3] << 3)
    return (mu >> x) & 1


def brute_flip(mul, inv, e, M, mu):
    n = len(mul)
    ctx = sorted({mul[inv[M[i]]][M[j]] for (i, j) in PAIRS})
    assert e not in ctx
    for vals in itertools.product((0, 1), repeat=len(ctx)):
        x = [0] * n
        for s, v in zip(ctx, vals):
            x[s] = v
        x2 = list(x)
        x2[e] = 1 - x2[e]
        same = True
        for g in range(n):
            b1 = [x[mul[g][m]] for m in M]
            b2 = [x2[mul[g][m]] for m in M]
            if rule_eval(mu, b1) != rule_eval(mu, b2):
                same = False
                break
        if same:
            return True
    return False


def main():
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    d = json.load(open(sys.argv[1]))
    parts = {tuple(p): k for k, p in enumerate(d["partitions"])}
    rules = {int(k): set(v) for k, v in d["rules"].items()}
    rule_list = sorted(rules)
    checked = agree = 0
    missing = 0
    for name, gens in GROUPS.items():
        mul, inv, e = perm_group(gens)
        n = len(mul)
        if n != EXPECTED_ORDERS[name] or n > 200:
            print("SKIP group", name, "order", n, "expected", EXPECTED_ORDERS[name])
            continue
        others = [g for g in range(n) if g != e]
        for trial in range(12):
            M = [e] + random.sample(others, 3)
            lab = [mul[inv[M[i]]][M[j]] for (i, j) in PAIRS]
            key = rgs(lab)
            if key not in parts:
                missing += 1
                print("MISSING partition", name, M, key)
                continue
            k = parts[key]
            for mu in random.sample(rule_list, 8):
                census_no_flip = k in rules[mu]
                brute = brute_flip(mul, inv, e, M, mu)
                checked += 1
                if brute == (not census_no_flip):
                    agree += 1
                else:
                    print("MISMATCH", name, M, mu, "census_no_flip", census_no_flip, "brute_flip", brute)
        print("group", name, "order", n, "checked so far", checked, "agree", agree)
    print(json.dumps({"checked": checked, "agree": agree, "missing_partitions": missing}))


if __name__ == "__main__":
    main()
