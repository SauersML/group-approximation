#!/usr/bin/env python3
"""Classify P(T) for every rook-independent table of shape at most 3x3.

After exact Tietze elimination (tietze.py) the presentation splits as a free
product along connected components of the generator/relator incidence graph
(generators occurring in no relator are free Z factors).  Each component is
recognized when it is
  * one generator:          Z/n with n = gcd of exponent sums (n = 0 means Z),
  * two generators, relator set {[a,b]}: Z^2,
and otherwise printed as an unrecognized factor for separate treatment.
"""
import json
import sys
from math import gcd

from tables import tables, gen_names
from tietze import simplify, canon, inv, reduce_mod_invol


def components(gens, rels):
    parent = {g: g for g in gens}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for r in rels:
        gs = sorted({abs(x) for x in r})
        for g in gs[1:]:
            a, b = find(gs[0]), find(g)
            if a != b:
                parent[a] = b
    comps = {}
    for g in gens:
        comps.setdefault(find(g), [set(), []])[0].add(g)
    for r in rels:
        comps[find(abs(r[0]))][1].append(r)
    return list(comps.values())


def invariant_factors(matrix, k):
    """Diagonal of the Smith normal form of an integer matrix with k columns."""
    A = [row[:] for row in matrix]
    diag = []
    r0 = 0
    for c0 in range(k):
        # find a nonzero entry in the submatrix
        while True:
            piv = None
            for i in range(r0, len(A)):
                for j in range(c0, k):
                    if A[i][j] != 0 and (piv is None or abs(A[i][j]) < abs(A[piv[0]][piv[1]])):
                        piv = (i, j)
            if piv is None:
                return diag + [0] * (k - len(diag))
            i, j = piv
            A[r0], A[i] = A[i], A[r0]
            for row in A:
                row[c0], row[j] = row[j], row[c0]
            p = A[r0][c0]
            done = True
            for i in range(len(A)):
                if i != r0 and A[i][c0]:
                    q = A[i][c0] // p
                    A[i] = [x - q * y for x, y in zip(A[i], A[r0])]
                    if A[i][c0]:
                        done = False
            for j in range(k):
                if j != c0 and A[r0][j]:
                    q = A[r0][j] // p
                    for row in A:
                        row[j] -= q * row[c0]
                    if A[r0][j]:
                        done = False
            if done:
                # enforce divisibility of the remaining block by p
                bad = [(i, j) for i in range(r0 + 1, len(A)) for j in range(c0 + 1, k)
                       if A[i][j] % p]
                if bad:
                    i, _ = bad[0]
                    A[r0] = [x + y for x, y in zip(A[r0], A[i])]
                    continue
                diag.append(abs(p))
                r0 += 1
                break
    return diag


def abelian_name(cg, crels):
    """If every pair of generators of the component has its commutator among the
    relators, the component is abelian: return its invariant-factor name."""
    invol = {abs(r[0]) for r in crels if len(r) == 2 and r[0] == r[1]}
    comms = set()
    for i, a in enumerate(cg):
        for b in cg[i + 1:]:
            c = canon(reduce_mod_invol((a, b, -a, -b), invol))
            if c:
                comms.add(c)
    if not comms <= set(crels):
        return None
    idx = {g: n for n, g in enumerate(cg)}
    rows = []
    for r in crels:
        v = [0] * len(cg)
        for x in r:
            v[idx[abs(x)]] += 1 if x > 0 else -1
        rows.append(v)
    d = invariant_factors(rows, len(cg))
    parts = [("Z" if t == 0 else f"Z/{t}") for t in d if t != 1]
    return "x".join(parts) if parts else "1"


def signed_images(w, a, b):
    """All images of w under the eight signed permutations of {a, b}."""
    out = set()
    for pa, pb in ((a, b), (b, a)):
        for ea in (1, -1):
            for eb in (1, -1):
                m = {a: ea * pa, b: eb * pb}
                out.add(canon(tuple((m[abs(x)] if x > 0 else -m[abs(x)]) for x in w)))
    return out


def recognize(cg, crels):
    cg = sorted(cg)
    if not crels:
        return "Z" if len(cg) == 1 else f"F{len(cg)}"
    if len(cg) == 1:
        n = 0
        for r in crels:
            n = gcd(n, abs(sum(1 if x > 0 else -1 for x in r)))
        return "Z" if n == 0 else ("1" if n == 1 else f"Z/{n}")
    ab = abelian_name(cg, crels)
    if ab is not None:
        return ab
    if len(cg) == 2 and len(crels) == 1:
        a, b = cg
        # Klein bottle group: <a,b | b a b^-1 = a^-1> and <a,b | a^2 = b^2>
        if crels[0] in signed_images((b, a, -b, a), a, b):
            return "K(bab^-1=a^-1)"
        if crels[0] in signed_images((a, a, -b, -b), a, b):
            return "K(a^2=b^2)"
    return None


def word_str(w, names):
    out = []
    for x in w:
        n = names[abs(x) - 1]
        out.append(n if x > 0 else n.upper())
    return "".join(out) if out else "1"


def main(out_path):
    summary = {}
    records = []
    for shape in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        names = gen_names(*shape)
        for tid, (part, rels) in enumerate(tables(*shape)):
            gens = list(range(1, len(names) + 1))
            g2, r2 = simplify(gens, rels)
            factors = []
            unknown = []
            for cg, crels in components(g2, r2):
                k = recognize(cg, crels)
                if k is None:
                    unknown.append({"gens": [names[g - 1] for g in sorted(cg)],
                                    "rels": [word_str(r, names) for r in crels]})
                else:
                    factors.append(k)
            rec = {"shape": list(shape), "id": tid,
                   "blocks": [[f"{s}|{m}" for (s, m) in b] for b in part if len(b) > 1],
                   "factors": sorted(factors), "unknown": unknown}
            records.append(rec)
            key = (shape, "known" if not unknown else "unknown")
            summary[key] = summary.get(key, 0) + 1
    with open(out_path, "w") as fh:
        for rec in records:
            fh.write(json.dumps(rec) + "\n")
    for k, v in sorted(summary.items()):
        print(k, v)


def main_ext(out_path, shapes):
    """Extended census with the direct generator (ids follow rook_partitions order).
    Writes only the tables with an unrecognized component, plus a factor summary."""
    from tables import tables_fast
    from collections import Counter
    from recognize_ext import certify_component
    kinds = Counter()
    unknown_types = Counter()
    cache = {}
    with open(out_path, "w") as fh:
        for shape in shapes:
            names = gen_names(*shape)
            n_known = n_unknown = 0
            for tid, (part, rels) in enumerate(tables_fast(*shape)):
                gens = list(range(1, len(names) + 1))
                g2, r2 = simplify(gens, rels)
                factors, unknown = [], []
                for cg, crels in components(g2, r2):
                    k = recognize(cg, crels)
                    if k is None:
                        key = (tuple(sorted(cg)), tuple(sorted(crels)))
                        if key not in cache:
                            cache[key] = certify_component(cg, crels)[0]
                        if cache[key] is not None:
                            factors.extend(cache[key])
                            continue
                        unknown.append({"ngens": len(cg),
                                        "rels": sorted(word_str(r, names) for r in crels)})
                    else:
                        factors.append(k)
                kinds[" * ".join(sorted(factors))] += 1
                if unknown:
                    n_unknown += 1
                    for u in unknown:
                        unknown_types[(u["ngens"], tuple(u["rels"]))] += 1
                    rec = {"shape": list(shape), "id": tid,
                           "blocks": [[f"{s}|{m}" for (s, m) in b] for b in part if len(b) > 1],
                           "factors": sorted(factors), "unknown": unknown}
                    fh.write(json.dumps(rec) + "\n")
                else:
                    n_known += 1
            print(shape, "known", n_known, "unknown", n_unknown)
    fam = Counter()
    for kind, c in kinds.items():
        for f in set(kind.split(" * ")):
            fam[f.split("(")[0] if f.startswith(("finite", "T(", "BS(")) else f] += c
    print("tables containing each factor family:", dict(sorted(fam.items())))
    names = Counter()
    for kind, c in kinds.items():
        for f in set(kind.split(" * ")):
            names[f] += c
    print("tables containing each factor name:", dict(sorted(names.items())))
    print("distinct free-product decompositions:", len(kinds))
    for kind, c in sorted(kinds.items(), key=lambda kv: -kv[1]):
        print("  decomposition", c, kind if kind else "(trivial group)")
    print("distinct unrecognized components:", len(unknown_types))
    for (ng, rs), c in unknown_types.most_common(40):
        print(c, ng, rs)


if __name__ == "__main__":
    if len(sys.argv) > 2:
        shapes = [tuple(int(t) for t in s.split("x")) for s in sys.argv[2].split(",")]
        main_ext(sys.argv[1], shapes)
    else:
        main(sys.argv[1] if len(sys.argv) > 1 else "classify.jsonl")
