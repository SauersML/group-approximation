#!/usr/bin/env python3
"""Extended recognition for components that classify.recognize leaves open.

Families recognized (every one is sofic, see the artifact, Section 5):
  finite(N)   Todd--Coxeter closes over the trivial subgroup (coset.py), the closed
              table is re-verified;
  T(p,q)      one relator on two generators with two syllables a^p b^q, |p|,|q| >= 2:
              <a,b | a^p = b^-q>, central extension of Z/p * Z/q by Z;
  BS(1,n)     one relator t^e a^m t^-e a^k with e = +-1 and min(|m|,|k|) = 1:
              a Baumslag--Solitar group BS(1,n), n = -k*m (metabelian);
  Z/n:Z       relators {a^n, t^e a^m t^-e a^k} with m, k units mod n: the semidirect
              product Z/n x| Z.
If a component is not recognized directly, a bounded breadth-first search over
elementary Nielsen moves (automorphisms of the free group on its generators, so the
presented group is unchanged), each followed by the exact simplification of
tietze.py, looks for a presentation whose components are all recognized.
"""
from collections import deque
from math import gcd

from classify import components, recognize
from coset import todd_coxeter, verify_action
from tietze import cyc_reduce, inv, normalize, simplify, substitute, total_len


def syllables(w):
    """Cyclic syllable decomposition [(generator, exponent), ...] of a cyclically
    reduced word, rotated so that it starts at a syllable boundary."""
    if not w:
        return []
    k = 0
    while k < len(w) and abs(w[k]) == abs(w[-1]):
        k += 1
        if k == len(w):
            return [(abs(w[0]), sum(1 if x > 0 else -1 for x in w))]
    u = w[k:] + w[:k]
    out = []
    for x in u:
        g, e = abs(x), (1 if x > 0 else -1)
        if out and out[-1][0] == g:
            out[-1][1] += e
        else:
            out.append([g, e])
    return [tuple(s) for s in out]


def relabel(cg, crels):
    """Rename the generators of a component to 1..k (a Tietze-free renaming)."""
    idx = {g: n + 1 for n, g in enumerate(sorted(cg))}
    rels = [tuple(idx[abs(x)] * (1 if x > 0 else -1) for x in r) for r in crels]
    return list(range(1, len(cg) + 1)), rels


def conj_form(r):
    """If r is cyclically t^e a^m t^-e a^k (e = +-1), return (t, a, m, k)."""
    sy = syllables(r)
    if len(sy) != 4:
        return None
    for rot in range(4):
        (t1, e1), (a1, m), (t2, e2), (a2, k) = sy[rot:] + sy[:rot]
        if t1 == t2 and a1 == a2 and t1 != a1 and abs(e1) == 1 and e2 == -e1:
            return t1, a1, m, k
    return None


def recognize2(cg, crels):
    name = recognize(cg, crels)
    if name is not None:
        return name
    gens, rels = relabel(cg, crels)
    try:
        n, perms = todd_coxeter(len(gens), rels, max_cosets=4000)
        if verify_action(n, perms, rels):
            return f"finite({n})"
    except OverflowError:
        pass
    if len(gens) == 2 and len(rels) == 1:
        sy = syllables(rels[0])
        if len(sy) == 2 and sy[0][0] != sy[1][0] and min(abs(sy[0][1]), abs(sy[1][1])) >= 2:
            p, q = sorted((abs(sy[0][1]), abs(sy[1][1])))
            return f"T({p},{q})"
        cf = conj_form(rels[0])
        if cf and min(abs(cf[2]), abs(cf[3])) == 1:
            return f"BS(1,{-cf[2] * cf[3]})"
    if len(gens) == 2 and len(rels) == 2:
        for i in (0, 1):
            sy = syllables(rels[i])
            cf = conj_form(rels[1 - i])
            if len(sy) == 1 and abs(sy[0][1]) >= 2 and cf and cf[1] == sy[0][0]:
                n = abs(sy[0][1])
                if gcd(cf[2], n) == 1 and gcd(cf[3], n) == 1:
                    return f"Z/{n}:Z"
    return None


def reduce_exponents(w, orders):
    """Rewrite each syllable g^k of w with g of finite order n = orders[g] (a relator
    g^n is present) as g^e, e = k mod n with |e| minimal.  The new word equals the
    old one modulo the relators g^n, so the normal closure is unchanged."""
    out = []
    for g, k in syllables(w):
        if g in orders:
            n = orders[g]
            k %= n
            if k > n // 2:
                k -= n
        out.extend([g if k > 0 else -g] * abs(k))
    return cyc_reduce(tuple(out))


def torsion_reduce(rels):
    """The power relators g^n (|n| >= 2) of one generator are replaced by the single
    relator g^gcd (same normal closure); every other relator is exponent-reduced
    modulo these orders and kept, even if it becomes a power word."""
    orders = {}
    others = []
    for r in rels:
        sy = syllables(r)
        if len(sy) == 1 and abs(sy[0][1]) >= 2:
            g, n = sy[0][0], abs(sy[0][1])
            orders[g] = gcd(orders.get(g, 0), n)
        else:
            others.append(r)
    out = [reduce_exponents(r, orders) for r in others]
    out += [tuple([g] * n) for g, n in orders.items()]
    new = normalize(out)
    if total_len(new) < total_len(normalize(rels)):
        return new, True
    return normalize(rels), False


def rotations(w):
    for u in (w, inv(w)):
        for i in range(len(u)):
            yield u[i:] + u[:i]


def pair_reduce(rels):
    """Replace a relator s by a cyclic reduction of r' s' (r', s' cyclic conjugates of
    r^{+-1}, s^{+-1}, r != s) when that is strictly shorter than s.  The normal closure
    is unchanged.  Applies the best such move once."""
    rels = normalize(rels)
    best = None
    for i, r in enumerate(rels):
        for j, s in enumerate(rels):
            if i == j:
                continue
            for r1 in rotations(r):
                for s1 in rotations(s):
                    t = cyc_reduce(r1 + s1)
                    if len(t) < len(s) and (best is None or len(s) - len(t) > best[0]):
                        best = (len(s) - len(t), j, t)
    if best is None:
        return rels, False
    _, j, t = best
    return normalize(rels[:j] + [t] + rels[j + 1:]), True


def simplify2(gens, rels):
    """tietze.simplify, then torsion exponent reduction and pairwise relator
    shortening, repeated while the total relator length strictly decreases."""
    gens, rels = simplify(gens, rels)
    while True:
        rels2, ok = torsion_reduce(rels)
        if not ok:
            rels2, ok = pair_reduce(rels)
        if not ok:
            return gens, rels
        gens, rels = simplify(gens, rels2)


def nielsen_neighbors(gens, rels):
    for x in gens:
        for y in gens:
            if x == y:
                continue
            for e in (1, -1):
                for repl in ((x, e * y), (e * y, x)):
                    yield normalize([substitute(r, x, repl) for r in rels])


def certify_component(cg, crels, slack=2, max_states=5000):
    """Return (sorted family names, number of states searched, final components) or
    (None, states, None).  The final components are the (generators, relators) of the
    presentation that was recognized; they present the component's group as a free
    product (homcheck34.py re-checks this by counting homomorphisms)."""
    start = (tuple(sorted(cg)), tuple(sorted(normalize(crels))))
    bound = total_len(start[1]) + slack
    seen = {start}
    queue = deque([start])
    while queue and len(seen) <= max_states:
        gens, rels = queue.popleft()
        g2, r2 = simplify2(list(gens), list(rels))
        names = []
        for c2, cr2 in components(g2, r2):
            k = recognize2(c2, cr2)
            if k is None:
                names = None
                break
            names.append(k)
        if names is not None:
            return sorted(names), len(seen), components(g2, r2)
        for new in nielsen_neighbors(list(gens), list(rels)):
            st = (gens, tuple(sorted(new)))
            if total_len(st[1]) <= bound and st not in seen:
                seen.add(st)
                queue.append(st)
    return None, len(seen), None


if __name__ == "__main__":
    tests = [
        ("BS(1,2)", [3, 1], [(-3, -1, 3, 1, 1)]),
        ("T(2,3)", [1, 2], [(-1, -1, 2, 1, 2)]),
        ("Z/3:Z", [2, 3], [(-3, 2, 3, 2), (2, 2, 2)]),
        ("Z*K", [1, 2, 3], [(-3, 1, -2, 1, -3, 2)]),
        ("S3", [2, 3], [(-2, 3, 2, 2, 3), (3, 3)]),
        ("Z/3:Z via pair", [1, 3], [(-1, 3, 1, 3), (-3, 1, 3, 3, -1)]),
        ("Z via pair", [2, 3], [(-3, -2, 3, 2, 2), (-3, 2, 3, 2, 2)]),
        ("Z/3*Z/2", [2, 3], [(-2, 3, 2, 2, 3), (2, 2, 2)]),
    ]
    for label, cg, crels in tests:
        print(label, certify_component(cg, crels))
