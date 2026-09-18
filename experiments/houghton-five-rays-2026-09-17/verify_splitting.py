#!/usr/bin/env python3
"""Machine check of the five-ray splitting lemma for Houghton pours.

Lemma (five rays). For distinct rays a,b,c,d,e and m1,m2 >= 1, the word
E^c_(a,b)(m) E^d_(a,b)(m)^(-1), m = m1+m2, is filled using

  3 route changes of size m1, 2 route changes of size m2, and
  exactly 4*m1*m2 + 4*m1 elementary relators
  ([lam_xy, lam_zw] with disjoint ray supports, or lam_xy lam_yx).

This script executes the derivation literally on words, for all 120 labelings
of the rays {1..5} and all 1 <= m1, m2 <= M. Each move is checked to be a
legal application of the stated relator type, and every intermediate word is
checked to represent the same permutation of Y_5 = [5] x N. Conventions follow
research/artifacts/zp-houghton-pours-2026-09-17.md: right actions, words read
left to right, lam_xy pulls ray x in and pushes ray y out.
"""
import itertools
import sys

RAYS = (1, 2, 3, 4, 5)


def lam_act(x, y, pt):
    r, p = pt
    if r == x:
        return (x, p - 1) if p >= 2 else (y, 1)
    if r == y:
        return (y, p + 1)
    return pt


def act(word, pt):
    for (x, y) in word:
        pt = lam_act(x, y, pt)
    return pt


def same_perm(w1, w2):
    depth = max(len(w1), len(w2)) + 4
    for r in RAYS:
        for p in range(1, depth + 1):
            if act(w1, (r, p)) != act(w2, (r, p)):
                return False
    return True


def pour(x, r, y, k):
    """E^r_(x,y)(k) = lam_xr^k lam_ry^k."""
    return [(x, r)] * k + [(r, y)] * k


class Derivation:
    def __init__(self, word):
        self.w = list(word)
        self.start = list(word)
        self.elem = 0
        self.route_changes = []

    def check(self):
        assert same_perm(self.w, self.start), "permutation changed"

    def insert_pair(self, pos, x, y):
        self.w[pos:pos] = [(x, y), (y, x)]
        self.elem += 1

    def cancel_pair(self, pos):
        (x, y), (u, v) = self.w[pos], self.w[pos + 1]
        assert (u, v) == (y, x), "not an inverse pair"
        del self.w[pos:pos + 2]
        self.elem += 1

    def swap(self, pos):
        s, t = self.w[pos], self.w[pos + 1]
        assert not (set(s) & set(t)), "ray supports meet: %r %r" % (s, t)
        self.w[pos], self.w[pos + 1] = t, s
        self.elem += 1

    def reroute(self, pos, x, r, y, k, r2):
        assert len({x, y, r, r2}) == 4, "quadruple not distinct"
        assert self.w[pos:pos + 2 * k] == pour(x, r, y, k), "no pour here"
        self.w[pos:pos + 2 * k] = pour(x, r2, y, k)
        self.route_changes.append(k)

    def move_block_right(self, pos, blen, olen):
        """Move block w[pos:pos+blen] right past the next olen letters."""
        for i in range(blen - 1, -1, -1):
            for j in range(olen):
                self.swap(pos + i + j)


def split_derivation(a, b, c, d, e, m1, m2):
    m = m1 + m2
    D = Derivation(pour(a, c, b, m))
    # A. Insert lam_ad^m1 lam_da^m1 after nothing (prefix) and
    #    lam_bd^m1 lam_db^m1 at the end, from the inside out.
    #    Prefix: lam_ac^m = [lam_ad^m1 lam_da^m1] lam_ac^m1 lam_ac^m2.
    for i in range(m1):
        D.insert_pair(i, a, d)  # at position i: nested insertion
    assert D.w[:2 * m1] == [(a, d)] * m1 + [(d, a)] * m1
    n = len(D.w)
    for i in range(m1):
        D.insert_pair(n + i, b, d)  # nested at the end: bd^m1 db^m1
    assert D.w[-2 * m1:] == [(b, d)] * m1 + [(d, b)] * m1
    D.check()
    P = m1                      # end of lam_ad^m1
    X0 = P                      # X_a = lam_da^m1 lam_ac^m1 at [P, P+2m1)
    Y0 = P + 2 * m1             # Y_c = lam_ac^m2 lam_cb^m2
    Z0 = Y0 + 2 * m2            # Z_b = lam_cb^m1 lam_bd^m1
    # B. Y_c -> Y_e.
    D.reroute(Y0, a, c, b, m2, e)
    # C. X_a -> X_b.
    D.reroute(X0, d, a, c, m1, b)
    D.check()
    # D. X_b past lam_ae^m2 (letters {d,b},{b,c} vs {a,e}).
    D.move_block_right(X0, 2 * m1, m2)
    X1 = X0 + m2
    # E. X_b -> X_a.
    D.reroute(X1, d, b, c, m1, a)
    # F. X_a past lam_eb^m2 (letters {d,a},{a,c} vs {e,b}).
    D.move_block_right(X1, 2 * m1, m2)
    X2 = X1 + m2
    D.check()
    # G. Z_b -> Z_a (Z now starts right after X_a).
    Z1 = X2 + 2 * m1
    assert Z1 == Z0
    D.reroute(Z1, c, b, d, m1, a)
    # H. X_a Z_a = lam_da^m1 lam_ac^m1 lam_ca^m1 lam_ad^m1 -> empty.
    for i in range(m1):
        D.cancel_pair(X2 + 2 * m1 - 1 - i)
    for i in range(m1):
        D.cancel_pair(X2 + m1 - 1 - i)
    D.check()
    # I. Y_e -> Y_d.
    D.reroute(P, a, e, b, m2, d)
    D.check()
    assert D.w == pour(a, d, b, m), "did not reach E^d_(a,b)(m)"
    return D


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    count = 0
    for (a, b, c, d, e) in itertools.permutations(RAYS):
        for m1 in range(1, M + 1):
            for m2 in range(1, M + 1):
                D = split_derivation(a, b, c, d, e, m1, m2)
                assert D.elem == 4 * m1 * m2 + 4 * m1, (D.elem, m1, m2)
                assert sorted(D.route_changes) == sorted([m1] * 3 + [m2] * 2)
                count += 1
    print("checked %d derivations (120 labelings, 1 <= m1,m2 <= %d)" % (count, M))
    print("each: 3 route changes of size m1, 2 of size m2, 4*m1*m2 + 4*m1 elementary relators")


if __name__ == "__main__":
    main()
