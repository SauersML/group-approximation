#!/usr/bin/env python3
"""Exact triage of the binary four-address single-flip census (flip1.json).

For each unbalanced rule class that passes the constant test and reads all four coordinates,
compute its minimal failing quotient partitions P.  Every group realization on which no single
invisible flip exists realizes a coarsening of some minimal failing P, so its memory group is a
quotient of the table group G_P = <a, b, c | q(rep)^-1 q(p) for p ~ rep>.

Each distinct minimal P is decided exactly, never guessed:
  * Tietze elimination of generators occurring once in a relator, plus Nielsen moves;
  * recognized forms: trivial, cyclic, free, free products of cyclic groups (word problem by
    syllable normal forms), free abelian of rank two;
  * otherwise a complete coset table with at most 3000 cosets, confirmed by the second strategy.
Amenable forms: finite, cyclic, Z/2 * Z/2, Z^2.  Non-amenable forms: free of rank >= 2, and free
products of cyclics with at least two nontrivial factors other than Z/2 * Z/2.
When the normal form is available we also compute the partition realized by the 12 quotients in
G_P and whether the four memory elements stay distinct.

A rule is EXCLUDED (injective implies balanced over every group) when every minimal failing P is
amenable or collapses the memory.  Otherwise the rule SURVIVES with its non-amenable or undecided
partitions listed.
"""
import itertools, json, sys
from collections import defaultdict

PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]
MEM = [(), (1,), (2,), (3,)]


def reduce(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def inv(w):
    return tuple(-g for g in reversed(w))


def mul(*ws):
    r = ()
    for w in ws:
        r = reduce(r + tuple(w))
    return r


def cyc_reduce(w):
    w = list(reduce(w))
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return tuple(w)


def quotient(i, j):
    return mul(inv(MEM[i]), MEM[j])


def classes_of(lbl):
    cl = defaultdict(list)
    for k, c in enumerate(lbl):
        cl[c].append(k)
    return list(cl.values())


def relators(lbl):
    rels = []
    for cls in classes_of(lbl):
        rep = quotient(*PAIRS[cls[0]])
        for k in cls[1:]:
            r = cyc_reduce(mul(inv(rep), quotient(*PAIRS[k])))
            if r:
                rels.append(r)
    return rels


def subst(w, g, img):
    out = ()
    for x in w:
        if x == g:
            out = mul(out, img)
        elif x == -g:
            out = mul(out, inv(img))
        else:
            out = mul(out, (x,))
    return out


def eliminate(gens, rels, sub):
    changed = True
    while changed:
        changed = False
        for r in rels:
            for g in gens:
                occ = [k for k, x in enumerate(r) if abs(x) == g]
                if len(occ) == 1:
                    k = occ[0]
                    u, e, v = r[:k], r[k], r[k + 1:]
                    img = mul(inv(u), inv(v)) if e > 0 else mul(v, u)
                    gens = [h for h in gens if h != g]
                    rels = [cyc_reduce(subst(s, g, img)) for s in rels]
                    rels = sorted({s for s in rels if s})
                    sub = {o: subst(w, g, img) for o, w in sub.items()}
                    changed = True
                    break
            if changed:
                break
    return gens, rels, sub


def free_product_orders(gens, rels):
    """If every relator is a power of one generator, return {gen: order (0 = infinite)}."""
    orders = {g: 0 for g in gens}
    from math import gcd
    for r in rels:
        if len({abs(x) for x in r}) != 1:
            return None
        g = abs(r[0])
        if not all(x == r[0] for x in r):
            return None
        orders[g] = gcd(orders[g], len(r))
    return orders


def fp_normal(w, orders):
    syl = []
    for x in w:
        g, e = abs(x), (1 if x > 0 else -1)
        if syl and syl[-1][0] == g:
            syl[-1][1] += e
        else:
            syl.append([g, e])
        n = orders[g]
        if n:
            syl[-1][1] %= n
        if syl[-1][1] == 0:
            syl.pop()
    # merging after pops can create new adjacent same-generator syllables
    changed = True
    while changed:
        changed = False
        out = []
        for g, e in syl:
            if out and out[-1][0] == g:
                out[-1][1] += e
                n = orders[g]
                if n:
                    out[-1][1] %= n
                if out[-1][1] == 0:
                    out.pop()
                changed = True
            else:
                out.append([g, e])
        syl = out
    return tuple((g, e) for g, e in syl)


def is_z2(gens, rels):
    if len(gens) != 2:
        return False
    g, h = gens
    targets = set()
    for a, b in ((g, h), (h, g)):
        c = (a, b, -a, -b)
        for k in range(4):
            targets.add(c[k:] + c[:k])
            ci = inv(c)
            targets.add(ci[k:] + ci[:k])
    return bool(rels) and all(r in targets for r in rels)


def cyc_fp_normal(w, orders):
    """Cyclic syllable normal form of w in the free product of cyclics with these orders."""
    nf = list(fp_normal(w, orders))
    guard = 0
    while len(nf) >= 2 and nf[0][0] == nf[-1][0] and guard < 1000:
        g, e = nf.pop()
        word = tuple([g if e > 0 else -g] * abs(e)) + syl_word(nf)
        nf = list(fp_normal(word, orders))
        guard += 1
    return tuple(nf)


def syl_word(syl):
    out = ()
    for g, e in syl:
        out += tuple([g if e > 0 else -g] * abs(e))
    return out


def power_normalize(gens, rels):
    """Split off pure-power relators, reduce the others modulo those orders, repeat.
    Returns (orders, remaining non-power relators) or None if nothing is left to reduce."""
    from math import gcd
    orders = {g: 0 for g in gens}
    rels = list(rels)
    for _ in range(20):
        new_orders = dict(orders)
        rest = []
        for r in rels:
            if r and len({abs(x) for x in r}) == 1 and all(x == r[0] for x in r):
                g = abs(r[0])
                new_orders[g] = gcd(new_orders[g], len(r))
            else:
                rest.append(r)
        normed = []
        for r in rest:
            nf = cyc_fp_normal(r, new_orders)
            if nf:
                w = syl_word(nf)
                normed.append(w)
        if new_orders == orders and normed == rels:
            return orders, normed
        orders, rels = new_orders, normed
    return orders, rels


def classify_form(gens, rels, sub):
    if not gens:
        return {"form": "trivial", "amenable": True, "memory_distinct": False}
    po, rest = power_normalize(gens, rels)
    if not rest:
        rels = [tuple([g] * n) for g, n in po.items() if n]
    orders = free_product_orders(gens, rels)
    if orders is not None:
        nontriv = [g for g in gens if orders[g] != 1]
        factors = sorted(orders[g] for g in nontriv)
        if len(nontriv) <= 1:
            amen = True
        elif factors == [2, 2]:
            amen = True
        else:
            amen = False
        nf = lambda w: fp_normal(w, orders)
        quots = [nf(subst_all(quotient(i, j), sub)) for (i, j) in PAIRS]
        mems = [nf(subst_all(m, sub)) for m in MEM]
        return {"form": "free-product-of-cyclics", "factors": factors, "amenable": amen,
                "memory_distinct": len(set(mems)) == 4,
                "realized": realized_partition(quots)}
    if is_z2(gens, rels):
        def vec(w):
            return tuple(sum((1 if x == g else -1) for x in w if abs(x) == g) for g in gens)
        quots = [vec(subst_all(quotient(i, j), sub)) for (i, j) in PAIRS]
        mems = [vec(subst_all(m, sub)) for m in MEM]
        return {"form": "Z2", "amenable": True, "memory_distinct": len(set(mems)) == 4,
                "realized": realized_partition(quots)}
    import gp
    cls, _nf = gp.classify(gens, rels, sub)
    if cls is not None:
        return cls
    return None


def subst_all(w, sub):
    out = ()
    for x in w:
        img = sub[abs(x)]
        out = mul(out, img if x > 0 else inv(img))
    return out


def realized_partition(quots):
    lab, seen = [], {}
    for q in quots:
        if q not in seen:
            seen[q] = len(seen)
        lab.append(seen[q])
    return lab


def nielsen_moves(gens):
    for i in gens:
        for j in gens:
            if i != j:
                for s in (1, -1):
                    yield i, (i, s * j)      # t = i j^s, so i = t j^-s
                    yield i, (s * j, i)      # t = j^s i, so i = j^-s t


def decide(rels):
    gens, rels0, sub = eliminate([1, 2, 3], rels, {1: (1,), 2: (2,), 3: (3,)})
    res = classify_form(gens, rels0, sub)
    if res:
        res["moves"] = 0
        return res
    frontier = [(gens, rels0, sub)]
    for depth in (1, 2, 3):
        nxt = []
        for gs, rs, sb in frontier:
            for i, newword in nielsen_moves(gs):
                # replace generator i by t = newword (keep the label i for t)
                a, b = newword
                if a == i:
                    img = (i, -b)
                else:
                    img = (-a, i)
                rs2 = sorted({cyc_reduce(subst(r, i, img)) for r in rs} - {()})
                sb2 = {o: subst(w, i, img) for o, w in sb.items()}
                gs3, rs3, sb3 = eliminate(list(gs), rs2, sb2)
                res = classify_form(gs3, rs3, sb3)
                if res:
                    res["moves"] = depth
                    return res
                nxt.append((gs3, rs3, sb3))
        frontier = nxt[:400]
    return None


def coset_decide(rels):
    from sympy.combinatorics.free_groups import free_group
    from sympy.combinatorics.fp_groups import FpGroup
    from sympy.combinatorics.coset_table import coset_enumeration_r, coset_enumeration_c
    F, a, b, c = free_group("a b c")
    gen = {1: a, 2: b, 3: c}

    def word(w):
        r = F.identity
        for x in w:
            r = r * (gen[x] if x > 0 else gen[-x] ** -1)
        return r

    G = FpGroup(F, [word(r) for r in rels])
    orders = []
    for enum in (coset_enumeration_r, coset_enumeration_c):
        try:
            C = enum(G, [], max_cosets=3000)
            C.compress()
            C.standardize()
            orders.append(len(C.table))
        except ValueError:
            orders.append(None)
    if orders[0] is not None and orders[0] == orders[1]:
        return {"form": "finite", "order": orders[0], "amenable": True}
    return {"form": "undecided", "coset_orders": orders}


def main():
    d = json.load(open(sys.argv[1]))
    parts = [tuple(p) for p in d["partitions"]]
    n = len(parts)

    def reads_all(mu):
        return all(any(((mu >> x) & 1) != ((mu >> (x ^ (1 << i))) & 1) for x in range(16))
                   for i in range(4))

    rules = {int(k): v for k, v in d["rules"].items()}
    kept = {mu: f for mu, f in rules.items() if reads_all(mu)}
    # strictly finer bitsets
    finer = [0] * n
    for p in range(n):
        for q in range(n):
            if p != q and parts[p] != parts[q]:
                lab = parts[q]
                if all(len({lab[k] for k in cls}) == 1 for cls in classes_of(parts[p])):
                    finer[q] |= 1 << p          # p strictly finer than q
    sys.stderr.write("finer bitsets done\n")
    minimal = {}
    for mu, f in kept.items():
        fb = 0
        for k in f:
            fb |= 1 << k
        minimal[mu] = [k for k in f if not (finer[k] & fb)]
    distinct = sorted({k for m in minimal.values() for k in m})
    sys.stderr.write("rules %d, distinct minimal %d\n" % (len(kept), len(distinct)))
    verdict = {}
    for k in distinct:
        rels = relators(parts[k])
        res = decide(rels)
        if res is None:
            res = coset_decide(rels)
        res["relators"] = [list(r) for r in rels]
        res["n_classes"] = len(set(parts[k]))
        verdict[k] = res
    with open("verdict_checkpoint.json", "w") as fh:
        json.dump({str(k): v for k, v in verdict.items()}, fh)
    survivors, excluded = {}, []
    for mu, m in minimal.items():
        bad = [k for k in m if not (verdict[k].get("amenable") is True
                                    or verdict[k].get("memory_distinct") is False)]
        if bad:
            survivors[mu] = bad
        else:
            excluded.append(mu)
    summary = {
        "rules_reading_all": len(kept),
        "excluded": len(excluded),
        "surviving": len(survivors),
        "distinct_minimal_partitions": len(distinct),
        "forms": dict(sorted(defaultdict(int, {}).items())),
    }
    forms = defaultdict(int)
    for v in verdict.values():
        forms[(v["form"], v.get("amenable"))] += 1
    summary["forms"] = {"%s|%s" % key: val for key, val in forms.items()}
    json.dump({"summary": summary, "excluded": sorted(excluded), "survivors": survivors,
               "minimal": minimal, "verdict": verdict}, sys.stdout)
    sys.stderr.write(json.dumps(summary) + "\n")


if __name__ == "__main__":
    main()
