#!/usr/bin/env python3
"""Search twisted triples in V for a quotient of G0/<<base>> in which a test relator survives.

Standard triple: a = (00 01), b = (01 10 11), c = (1 00).  A twisted triple keeps the cone
combinatorics but composes with permutations of the next d digits:
  a'(00u) = 01 alpha(u),  a'(01u) = 00 alpha^-1(u)            (so a'^2 = 1)
  b' = b                                                     (b'^3 = (a'b')^4 checked)
  c'(1u)  = 00 psi(u),    c'(00u) = 1 psi^-1(u),  c' = id on 01 (so c'^2 = 1)
with alpha, psi permutations of {0,1}^d.  Each twisted element lies in V.  For every choice we
test the base relators exactly (as prefix maps on all cylinders); for survivors we report which
test relators act nontrivially.  A survivor with a nontrivial test relator is an honest
homomorphism G0/<<base>> -> V killing base but not the test word, so the test word is not in
<<base>>.

usage: twisted_triples.py d base_csv test_csv [twist_a(0/1)]
"""
import itertools
import sys

import prefix_cocycles as pc


def make_rules(d, alpha, psi):
    strs = ["".join(t) for t in itertools.product("01", repeat=d)]
    ainv = {v: u for u, v in alpha.items()}
    pinv = {v: u for u, v in psi.items()}
    ra = [("00" + u, "01" + alpha[u]) for u in strs] + [("01" + u, "00" + ainv[u]) for u in strs] + [("1", "1")]
    rb = list(pc.RULES[("b", 1)])
    rc = [("1" + u, "00" + psi[u]) for u in strs] + [("00" + u, "1" + pinv[u]) for u in strs] + [("01", "01")]
    rules = {("a", 1): ra, ("b", 1): rb, ("c", 1): rc}
    for g in "abc":
        rules[(g, -1)] = [(q, p) for p, q in rules[(g, 1)]]
    return rules


def act(rules, s, letter):
    for p, q in rules[letter]:
        if s.startswith(p):
            return q + s[len(p):]
        if p.startswith(s):
            return None
    raise AssertionError((s, letter))


def trivial_on(rules, word, limit=4000):
    """True if word acts as identity; else (False, cylinder).  None if too many cylinders."""
    stack = [""]
    count = 0
    while stack:
        p0 = stack.pop()
        count += 1
        if count > limit:
            return None
        s = p0
        ok = True
        for g, e in word:
            t = act(rules, s, (g, e))
            if t is None:
                ok = False
                break
            s = t
        if not ok:
            stack.append(p0 + "0")
            stack.append(p0 + "1")
            continue
        if s != p0:
            return (False, p0)
    return True


def perms_of(d):
    strs = ["".join(t) for t in itertools.product("01", repeat=d)]
    for img in itertools.permutations(strs):
        yield dict(zip(strs, img))


def main():
    d = int(sys.argv[1])
    base = sys.argv[2].split(",")
    tests = sys.argv[3].split(",")
    twist_a = len(sys.argv) > 4 and sys.argv[4] == "1"
    strs = ["".join(t) for t in itertools.product("01", repeat=d)]
    ident = {u: u for u in strs}
    alphas = list(perms_of(d)) if twist_a else [ident]
    n_sat = 0
    n_tot = 0
    hits = []
    for alpha in alphas:
        for psi in perms_of(d):
            n_tot += 1
            rules = make_rules(d, alpha, psi)
            good = True
            for name in base:
                r = trivial_on(rules, pc.WORDS[name])
                if r is not True:
                    good = False
                    break
            if not good:
                continue
            n_sat += 1
            bad = []
            for name in tests:
                r = trivial_on(rules, pc.WORDS[name])
                if r is not True:
                    bad.append((name, r))
            if bad:
                hits.append((alpha, psi, bad))
                print("HIT", alpha, psi, bad, flush=True)
    print({"d": d, "twist_a": twist_a, "base": base, "tests": tests, "tried": n_tot,
           "satisfy_base": n_sat, "hits": len(hits)})


if __name__ == "__main__":
    main()
