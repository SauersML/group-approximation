#!/usr/bin/env python3
"""Classify binary three-address rules and sanity-check the kill lemmas on finite groups.

Convention: tau(x)(h) = mu(x(h m0), x(h m1), x(h m2)); mu is indexed by x0*4 + x1*2 + x2.

Part 1 (group-free): list balanced rules on three effective addresses with mu(000) != mu(111),
normalized to mu(000) = 0, and record which universal test applies:
  T1  single-site flip on a constant background is invisible;
  C   coset background (Lemma C): mu(e_p+e_q) = mu(e_r) = mu(000), or mu(e_r) = mu(e_p+e_q) = mu(111);
  AFF affine rule;  A  remaining (expected: the three 'selector ? AND : OR' rules).
Part 2 (finite groups): brute-force injectivity and compare with the predictions of the lemmas.
"""
import itertools, sys
import numpy as np

def idx(bits):
    return bits[0] * 4 + bits[1] * 2 + bits[2]

def depends_all(mu):
    for i in range(3):
        if all(mu[idx(b)] == mu[idx(tuple(1 - b[j] if j == i else b[j] for j in range(3)))]
               for b in itertools.product((0, 1), repeat=3)):
            return False
    return True

def is_affine(mu):
    for c in itertools.product((0, 1), repeat=4):
        if all(mu[idx(b)] == (c[0] + c[1] * b[0] + c[2] * b[1] + c[3] * b[2]) % 2
               for b in itertools.product((0, 1), repeat=3)):
            return True
    return False

E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

def t1(mu):
    z, o = mu[0], mu[7]
    return all(mu[idx(e)] == z for e in E) or all(mu[idx(tuple(1 - v for v in e))] == o for e in E)

def lemma_c_triples(mu):
    """Ordered (p, q, r) for which the coset background test applies (either background)."""
    out = []
    for r in range(3):
        p, q = [i for i in range(3) if i != r]
        pq = tuple(1 if j in (p, q) else 0 for j in range(3))
        er = E[r]
        if mu[idx(pq)] == mu[idx(er)] == mu[0] or mu[idx(er)] == mu[idx(pq)] == mu[7]:
            out.append((p, q, r))
            out.append((q, p, r))
    return out

def classify():
    rows = []
    for tab in itertools.product((0, 1), repeat=8):
        mu = tab
        if mu[0] != 0 or mu[7] != 1 or sum(mu) != 4 or not depends_all(mu):
            continue
        if is_affine(mu):
            kind = "AFF"
        elif t1(mu):
            kind = "T1"
        elif lemma_c_triples(mu):
            kind = "C"
        else:
            kind = "A"
        rows.append((mu, kind))
    return rows

def selector_and_or(mu):
    """Return s if mu = x_s ? AND(other two) : OR(other two), else None."""
    for s in range(3):
        o = [i for i in range(3) if i != s]
        ok = True
        for b in itertools.product((0, 1), repeat=3):
            u, v = b[o[0]], b[o[1]]
            val = (u & v) if b[s] else (u | v)
            if mu[idx(b)] != val:
                ok = False
                break
        if ok:
            return s
    return None

if __name__ == "__main__":
    rows = classify()
    counts = {}
    for mu, kind in rows:
        counts[kind] = counts.get(kind, 0) + 1
        extra = ""
        if kind == "A":
            extra = " selector=%s" % selector_and_or(mu)
        print("".join(map(str, mu)), kind, extra)
    print("total", len(rows), counts)
    sys.stdout.flush()
