#!/usr/bin/env python3
"""Search homomorphisms G0/<<base>> -> V built from rigid cone permutations.

Every finite subgroup of V is conjugate into the rigid permutation group of the cones of some
complete prefix code.  We search triples (a, b, c) of elements of V with
  <a, b> acting as rigid permutations of the cones of a complete prefix code P,
  <a, c> acting as rigid permutations of the cones of a complete prefix code Q,
so that a^2, b^3, (ab)^4 hold as permutations of P and c^2, (ac)^3 hold as permutations of Q
(both then hold exactly in V).  For each such triple we check the base words exactly as prefix
maps; a survivor on which a test word acts nontrivially is a homomorphism G0/<<base>> -> V that
does not kill that word, so the word is not in <<base>>.

usage: rigid_triples.py maxdepth maxP maxQ base_csv test_csv
"""
import itertools
import sys

import prefix_cocycles as pc
from twisted_triples import trivial_on


def codes(maxdepth):
    """All complete binary prefix codes with word length <= maxdepth, as sorted tuples."""
    def rec(prefix, d):
        yield (prefix,)
        if d < maxdepth:
            for left in rec(prefix + "0", d + 1):
                for right in rec(prefix + "1", d + 1):
                    yield left + right
    out = []
    for c in rec("", 0):
        out.append(tuple(sorted(c)))
    return out


def compose(p, q):
    """Right action: x.(pq) = (x.p).q, perms as tuples."""
    return tuple(q[p[i]] for i in range(len(p)))


def order_divides(p, n):
    x = tuple(range(len(p)))
    for _ in range(n):
        x = compose(x, p)
    return x == tuple(range(len(p)))


def rigid_perm_on(rules, Q):
    """If the rigid map given by `rules` (a list of (p, q) on some code) maps each cone of Q rigidly
    onto a cone of Q, return the permutation of Q; else None."""
    img = []
    idx = {q: i for i, q in enumerate(Q)}
    for q in Q:
        target = None
        for p, r in rules:
            if q.startswith(p):
                target = r + q[len(p):]
                break
        if target is None:
            # q is refined by the rules: rigid iff every p = q u maps to t u for one common t
            ts = set()
            for p, r in rules:
                if p.startswith(q):
                    u = p[len(q):]
                    if len(r) < len(u) or not r.endswith(u):
                        return None
                    ts.add(r[:len(r) - len(u)])
            if len(ts) != 1:
                return None
            target = ts.pop()
        if target not in idx:
            return None
        img.append(idx[target])
    if sorted(img) != list(range(len(Q))):
        return None
    return tuple(img)


def rules_of(code, perm):
    rules = [(code[i], code[perm[i]]) for i in range(len(code))]
    return rules


def make(rules_a, rules_b, rules_c):
    R = {("a", 1): rules_a, ("b", 1): rules_b, ("c", 1): rules_c}
    for g in "abc":
        R[(g, -1)] = [(q, p) for p, q in R[(g, 1)]]
    return R


def main():
    maxdepth = int(sys.argv[1])
    maxP = int(sys.argv[2])
    maxQ = int(sys.argv[3])
    base = sys.argv[4].split(",")
    tests = sys.argv[5].split(",")
    allcodes = codes(maxdepth)
    Ps = [c for c in allcodes if 2 <= len(c) <= maxP]
    Qs = [c for c in allcodes if 2 <= len(c) <= maxQ]
    stats = {"ab_pairs": 0, "triples": 0, "base_ok": 0, "hits": 0}
    seen = set()
    for P in Ps:
        n = len(P)
        perms = list(itertools.permutations(range(n)))
        invols = [p for p in perms if order_divides(p, 2)]
        ord3 = [p for p in perms if order_divides(p, 3)]
        for pa in invols:
            ra = rules_of(P, pa)
            # the a-action on each Q
            qa = []
            for Q in Qs:
                t = rigid_perm_on(ra, Q)
                if t is not None:
                    qa.append((Q, t))
            if not qa:
                continue
            for pb in ord3:
                if not order_divides(compose(pa, pb), 4):
                    continue
                if pa == tuple(range(n)) and pb == tuple(range(n)):
                    continue
                stats["ab_pairs"] += 1
                rb = rules_of(P, pb)
                for Q, ta in qa:
                    m = len(Q)
                    for pc_ in itertools.permutations(range(m)):
                        if not order_divides(pc_, 2):
                            continue
                        if not order_divides(compose(ta, pc_), 3):
                            continue
                        rc = rules_of(Q, pc_)
                        key = (tuple(sorted(ra)), tuple(sorted(rb)), tuple(sorted(rc)))
                        if key in seen:
                            continue
                        seen.add(key)
                        stats["triples"] += 1
                        R = make(ra, rb, rc)
                        good = True
                        for nm in base:
                            if trivial_on(R, pc.WORDS[nm], limit=20000) is not True:
                                good = False
                                break
                        if not good:
                            continue
                        stats["base_ok"] += 1
                        bad = []
                        for nm in tests:
                            r = trivial_on(R, pc.WORDS[nm], limit=20000)
                            if r is None:
                                stats["unknown"] = stats.get("unknown", 0) + 1
                            elif r is not True:
                                bad.append((nm, r))
                        if bad:
                            stats["hits"] += 1
                            if stats["hits"] <= 20:
                                print("HIT", {"a": ra, "b": rb, "c": rc, "bad": bad}, flush=True)
    print({"maxdepth": maxdepth, "maxP": maxP, "maxQ": maxQ, "base": base, "tests": tests, **stats})


if __name__ == "__main__":
    main()
