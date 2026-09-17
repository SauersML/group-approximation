#!/usr/bin/env python3
"""Calibration of the ball-table construction on BS(2,3) = < a, t | t^-1 a^2 t = a^3 >.

research/three-point-memory-table-certificates-are-universal-proof.md, Section 4, uses the forward table
T = T_f(K) of K = BS(2,3) with decoder labels S = {1, a, t} and encoder labels M = B_K(4). This script

  1. decides equality in K by Britton's lemma (a word is trivial iff pinch reduction empties it),
  2. enumerates the ball B_K(4) with one geodesic word per element,
  3. builds the forward table on S x M, checks rook independence and counts its classes,
  4. checks that every edge relator used by the proof is a cell pair of T
     (for eps in {a, t} and m, eps m in M: (eps, m) ~ (1, eps m);
      for m, eps^-1 m in M: (eps, eps^-1 m) ~ (1, m)),
  5. checks that the words of the relator t^-1 a^2 t = a^3 have all suffixes in M, so the relator holds in P(T),
  6. checks that au != ua in K (u = t^-1 a t), both in M, so (au, 1) and (ua, 1) are distinct reverse products,
  7. sanity check, not used by the proof: in every homomorphism K -> S_n, n <= 5, the images of au and ua agree.

usage: python3 ballcal.py
"""
import itertools
import sys

GENS = {"a": ("a", 1), "A": ("a", -1), "t": ("t", 1), "T": ("t", -1)}


def reduce_word(word):
    """Britton reduction. word: string over a A t T. Returns list of items: ('a', k) or ('t', +-1)."""
    stack = []
    for ch in word:
        g, e = GENS[ch]
        if g == "a":
            if stack and stack[-1][0] == "a":
                k = stack[-1][1] + e
                stack.pop()
                if k:
                    stack.append(("a", k))
            else:
                stack.append(("a", e))
        else:
            item = ("t", e)
            # try a pinch t^(-e) a^k t^e, or a free cancellation t^(-e) t^e
            if stack and stack[-1] == ("t", -e):
                stack.pop()
                continue
            if len(stack) >= 2 and stack[-1][0] == "a" and stack[-2] == ("t", -e):
                k = stack[-1][1]
                # e = +1: t^-1 a^k t with 2 | k -> a^(3k/2); e = -1: t a^k t^-1 with 3 | k -> a^(2k/3)
                if e == 1 and k % 2 == 0:
                    new = 3 * k // 2
                elif e == -1 and k % 3 == 0:
                    new = 2 * k // 3
                else:
                    stack.append(item)
                    continue
                stack.pop()
                stack.pop()
                if stack and stack[-1][0] == "a":
                    new += stack[-1][1]
                    stack.pop()
                if new:
                    stack.append(("a", new))
                continue
            stack.append(item)
    return stack


def inverse(word):
    return "".join({"a": "A", "A": "a", "t": "T", "T": "t"}[c] for c in reversed(word))


def trivial(word):
    return reduce_word(word) == []


def equal(u, v):
    return trivial(u + inverse(v))


def ball(radius):
    """One geodesic word per element of B(radius), in order of length."""
    reps = [""]
    frontier = [""]
    for _ in range(radius):
        new = []
        for w in frontier:
            for c in "aAtT":
                x = c + w  # left multiplication, as in the proof's paths m -> eps m
                if any(equal(x, r) for r in reps):
                    continue
                reps.append(x)
                new.append(x)
        frontier = new
    return reps


def index_of(word, reps):
    for i, r in enumerate(reps):
        if equal(word, r):
            return i
    return None


def main():
    R = 4
    M = ball(R)
    sizes = [sum(1 for w in M if len(w) <= r) for r in range(R + 1)]
    print("ball sizes |B(r)|, r = 0..4:", sizes)
    S = ["", "a", "t"]
    # forward products s m, classed by equality in K
    products = []
    cls = {}
    for si, s in enumerate(S):
        for mi, m in enumerate(M):
            w = s + m
            for key, rep in products:
                if equal(w, rep):
                    cls[(si, mi)] = key
                    break
            else:
                key = len(products)
                products.append((key, w))
                cls[(si, mi)] = key
    ncls = len(products)
    # rook independence
    ok = True
    for si in range(3):
        vals = [cls[(si, mi)] for mi in range(len(M))]
        ok &= len(set(vals)) == len(vals)
    for mi in range(len(M)):
        vals = [cls[(si, mi)] for si in range(3)]
        ok &= len(set(vals)) == len(vals)
    print("table shape 3 x %d, %d cells, %d classes, rook independent: %s" % (len(M), 3 * len(M), ncls, ok))
    if not ok:
        sys.exit(1)
    # labels distinct
    assert all(not equal(M[i], M[j]) for i in range(len(M)) for j in range(i))
    assert index_of("a", M) is not None and index_of("t", M) is not None
    # edge relators
    edges = 0
    for si, eps in [(1, "a"), (2, "t")]:
        for mi, m in enumerate(M):
            j = index_of(eps + m, M)
            if j is not None:
                assert cls[(si, mi)] == cls[(0, j)]
                edges += 1
            j = index_of(inverse(eps) + m, M)
            if j is not None:
                assert cls[(si, j)] == cls[(0, mi)]
    print("edge relators (eps, m) ~ (1, eps m) present:", edges)
    # relator words: suffixes in M
    for w in ["TaatAAA", "aaa", "Taat"]:
        for k in range(len(w) + 1):
            suf = w[len(w) - k:]
            if len(suf) <= R:
                assert index_of(suf, M) is not None, suf
    assert trivial("TaatAAA")
    print("relator t^-1 a^2 t = a^3: both sides' suffixes lie in M")
    au, ua = "aTat", "Tata"
    ia, iu = index_of(au, M), index_of(ua, M)
    assert ia is not None and iu is not None and ia != iu
    assert not trivial(au + inverse(ua))
    print("au = %s and ua = %s are distinct elements of M" % (au, ua))
    # sanity: homomorphisms to S_n
    for n in range(2, 6):
        perms = list(itertools.permutations(range(n)))
        comp = lambda p, q: tuple(p[q[i]] for i in range(n))  # p after q
        inv = lambda p: tuple(sorted(range(n), key=lambda i: p[i]))
        homs = 0
        bad = 0
        for pa in perms:
            a2 = comp(pa, pa)
            a3 = comp(pa, a2)
            for pt in perms:
                ti = inv(pt)
                # word t^-1 a^2 t read left to right acts as right multiplication; any consistent convention works
                if comp(comp(ti, a2), pt) != a3:
                    continue
                homs += 1
                pu = comp(comp(ti, pa), pt)
                if comp(pa, pu) != comp(pu, pa):
                    bad += 1
        print("S_%d: %d homomorphisms, images of au and ua differ in %d" % (n, homs, bad))
        assert bad == 0


if __name__ == "__main__":
    main()
