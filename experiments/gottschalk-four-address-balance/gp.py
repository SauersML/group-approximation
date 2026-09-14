#!/usr/bin/env python3
"""Recognize graph products of cyclic groups and cyclic-by-cyclic two-generator groups.

Input: remaining generators `gens`, relators `rels` (tuples of +-gen), substitution `sub`
(original generator -> word), after Tietze elimination.

* power relators g^n set orders; other relators are reduced modulo those orders;
* if every other relator is a commutator [g^e, h^f] with e, f generating <g>, <h>, the group is
  the graph product of the cyclic groups <g> (order n or infinite) over the commutation graph.
  - amenable iff every component of the NON-commutation graph is one vertex, or two vertices
    of order 2 (D_infinity): special subgroups embed, <u, v> = G_u * G_v for non-commuting u, v,
    and a non-commuting path u - v - w gives (G_u x G_w) * G_v or G_u * G_v * G_w;
  - word problem: merge same-generator syllables separated only by commuting syllables, then
    take the greedy lexicographic shuffle representative (Green's normal form theorem);
* if there are two generators and some relator is a rotation of h^-1 g h g^-k with k = +-1,
  then <g> is normal with cyclic quotient, so the group is cyclic-by-cyclic and amenable.
"""
from math import gcd
import analyze2 as A


def syllables(w):
    syl = []
    for x in w:
        g, e = abs(x), (1 if x > 0 else -1)
        if syl and syl[-1][0] == g:
            syl[-1][1] += e
            if syl[-1][1] == 0:
                syl.pop()
        else:
            syl.append([g, e])
    return syl


def norm_exp(e, n):
    return e % n if n else e


def gp_reduce(syl, orders, commute):
    syl = [[g, norm_exp(e, orders[g])] for g, e in syl]
    syl = [s for s in syl if s[1] != 0]
    changed = True
    while changed:
        changed = False
        for i in range(len(syl)):
            g = syl[i][0]
            for j in range(i + 1, len(syl)):
                h = syl[j][0]
                if h == g:
                    syl[i][1] = norm_exp(syl[i][1] + syl[j][1], orders[g])
                    del syl[j]
                    if syl[i][1] == 0:
                        del syl[i]
                    changed = True
                    break
                if (g, h) not in commute:
                    break
            if changed:
                break
    return syl


def gp_normal(w, orders, commute):
    syl = gp_reduce(syllables(w), orders, commute)
    out = []
    rest = [tuple(s) for s in syl]
    while rest:
        cands = []
        for k, (g, e) in enumerate(rest):
            if all((rest[t][0], g) in commute for t in range(k)):
                cands.append(((g, e), k))
        (g, e), k = min(cands)
        out.append((g, e))
        del rest[k]
    return tuple(out)


def rotations(syl):
    return [syl[k:] + syl[:k] for k in range(len(syl))]


def as_commutator(r, orders):
    syl = syllables(r)
    syl = [[g, norm_exp(e, orders[g])] for g, e in syl]
    syl = [s for s in syl if s[1] != 0]
    # merge cyclic ends
    while len(syl) >= 2 and syl[0][0] == syl[-1][0]:
        g, e = syl.pop()
        syl[0][1] = norm_exp(syl[0][1] + e, orders[g])
        if syl[0][1] == 0:
            syl.pop(0)
    if len(syl) != 4:
        return None
    (g1, e1), (h1, f1), (g2, e2), (h2, f2) = syl
    if not (g1 == g2 and h1 == h2 and g1 != h1):
        return None
    if norm_exp(e1 + e2, orders[g1]) != 0 or norm_exp(f1 + f2, orders[h1]) != 0:
        return None

    def generates(e, n):
        return abs(e) == 1 if n == 0 else gcd(e, n) == 1

    if generates(e1, orders[g1]) and generates(f1, orders[h1]):
        return (g1, h1)
    return None


def as_normalizer(r, orders):
    """Rotation of h^-1 g h g^-k (k = +-1) or its inverse, on two distinct generators."""
    syl = syllables(r)
    while len(syl) >= 2 and syl[0][0] == syl[-1][0]:
        g, e = syl.pop()
        syl[0][1] += e
        if syl[0][1] == 0:
            syl.pop(0)
    for rot in rotations(syl) + rotations([[g, -e] for g, e in reversed(syl)]):
        if len(rot) == 4:
            (h1, a1), (g1, b1), (h2, a2), (g2, b2) = rot
            if h1 == h2 and g1 == g2 and h1 != g1 and a1 == -1 and a2 == 1 and b1 == 1 and b2 in (1, -1):
                return (g1, h1)
    return None


def classify(gens, rels, sub):
    if not gens:
        return {"form": "trivial", "amenable": True, "memory_distinct": False}, None
    po, rest = A.power_normalize(gens, rels)
    orders = dict(po)
    live = [g for g in gens if orders[g] != 1]
    commute = set()
    for g in live:
        commute.add((g, g))
    ok = True
    for r in rest:
        r2 = tuple(x for x in r if orders[abs(x)] != 1)
        if not r2:
            continue
        c = as_commutator(r2, orders)
        if c is None:
            ok = False
            break
        commute.add(c)
        commute.add((c[1], c[0]))
    if ok:
        # complement components
        comp, seen = [], set()
        for g in live:
            if g in seen:
                continue
            stack, cc = [g], []
            seen.add(g)
            while stack:
                u = stack.pop()
                cc.append(u)
                for v in live:
                    if v not in seen and (u, v) not in commute:
                        seen.add(v)
                        stack.append(v)
            comp.append(cc)
        amen = all(len(cc) == 1 or (len(cc) == 2 and all(orders[u] == 2 for u in cc)) for cc in comp)

        def nf(w, orders=orders, commute=commute, sub=sub):
            v = tuple(x for x in A.subst_all(w, sub) if orders[abs(x)] != 1)
            return gp_normal(v, orders, commute)

        mems = [nf(m) for m in A.MEM]
        quots = [nf(A.quotient(i, j)) for (i, j) in A.PAIRS]
        return {"form": "graph-product-of-cyclics", "orders": [orders[g] for g in live],
                "components": [len(cc) for cc in comp], "amenable": amen,
                "memory_distinct": len(set(mems)) == 4,
                "realized": A.realized_partition(quots)}, nf
    if len(live) == 2:
        for r in rest:
            if as_normalizer(r, orders):
                return {"form": "cyclic-by-cyclic", "amenable": True}, None
    return None, None


if __name__ == "__main__":
    tests = {
        "Z*(Z2xZ2) p940": ([1, 2, 3], [(-2, -2), (-3, -3), (-3, 2, -3, 2)]),
        "Klein p967": ([1, 3], [(-3, 1, 3, 1), (3, 1, -3, 1)]),
        "Klein p719": ([2, 3], [(-3, -2, -3, 2), (-2, -3, 2, -3)]),
        "(Z2)^3 RACG complete": ([1, 2, 3], [(1, 1), (2, 2), (3, 3), (1, 2, 1, 2), (1, 3, 1, 3), (2, 3, 2, 3)]),
        "RACG path a-b-c noncommuting": ([1, 2, 3], [(1, 1), (2, 2), (3, 3), (1, 3, 1, 3)]),
        "Z2 x Dinf": ([1, 2, 3], [(1, 1), (2, 2), (3, 3), (1, 2, 1, 2), (1, 3, 1, 3)]),
    }
    for name, (gens, rels) in tests.items():
        sub = {1: (1,), 2: (2,), 3: (3,)}
        cls, nf = classify(gens, [A.cyc_reduce(r) for r in rels], sub)
        print(name, cls)
    # normal form sanity in Z x Z: ab = ba, a b a^-1 = b
    cls, nf = classify([1, 2], [(1, 2, -1, -2)], {1: (1,), 2: (2,), 3: ()})
    print("ZxZ ab==ba", nf((1, 2)) == nf((2, 1)), "aba'==b", nf((1, 2, -1)) == nf((2,)), "ab!=a", nf((1, 2)) != nf((1,)))
    cls, nf = classify([1, 2, 3], [(1, 1), (2, 2), (3, 3), (1, 3, 1, 3)], {1: (1,), 2: (2,), 3: (3,)})
    print("RACG ac==ca", nf((1, 3)) == nf((3, 1)), "ab!=ba", nf((1, 2)) != nf((2, 1)), "abba==1", nf((1, 2, 2, 1)) == nf(()), "acbca==b?", nf((1, 3, 2, 3, 1)) == nf((2,)))
