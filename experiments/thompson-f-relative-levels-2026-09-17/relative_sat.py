"""SAT check: does any weak order on the middle leaves satisfy every monotone-pair rule?

A configuration of a relative model is a weak order h on the n middle leaves (any number of
levels, realised by integer levels, reals, or lexicographic multi-scale vectors) together with
positive weights; the rules of relative_rules.py do not depend on the weights.  For a monotone
pair (s, t, i, j) with Y = p_j(s) ⊇ Y' = p_j(t) and X = p_i(s) ⊆ X' = p_i(t):

  [H_Y > H_X] == [H_Y' > H_X'],   [H_Y >= H_X] == [H_Y' >= H_X'],
  and on a tie every leaf of (Y \\ Y') ∪ (X' \\ X) lies strictly below H_X.

Variables ge[u][v] = [h_u >= h_v], with totality and transitivity; every other quantity is a
Tseitin auxiliary.  UNSAT means no configuration of any relative model survives the rules.

Usage: python3 relative_sat.py m d [--drop k]   (--drop: also test every rule set with one pair
       family removed, to see which rules are needed)
"""
import itertools
import sys

from pysat.formula import IDPool
from pysat.solvers import Minisat22

from relative_level_lp import setup
from relative_rules import monotone_pairs


class Enc:
    def __init__(self, n):
        self.n = n
        self.pool = IDPool()
        self.cl = []
        for u, v in itertools.permutations(range(n), 2):
            if u < v:
                self.cl.append([self.ge(u, v), self.ge(v, u)])
        for u, v, w in itertools.permutations(range(n), 3):
            self.cl.append([-self.ge(u, v), -self.ge(v, w), self.ge(u, w)])

    def ge(self, u, v):
        return self.pool.id(("ge", u, v))

    def AND(self, lits, tag):
        a = self.pool.id(tag)
        for l in lits:
            self.cl.append([-a, l])
        self.cl.append([a] + [-l for l in lits])
        return a

    def OR(self, lits, tag):
        a = self.pool.id(tag)
        for l in lits:
            self.cl.append([a, -l])
        self.cl.append([-a] + list(lits))
        return a

    def lit(self, u, v, strict):
        """[h_u > h_v] if strict else [h_u >= h_v]; u == v gives constant."""
        if u == v:
            return None if strict else True
        return -self.ge(v, u) if strict else self.ge(u, v)

    def cmp(self, Y, X, strict):
        """[H_Y > H_X] (strict) or [H_Y >= H_X]."""
        Y, X = tuple(sorted(Y)), tuple(sorted(X))
        terms = []
        for u in Y:
            ls = [self.lit(u, x, strict) for x in X]
            if None in ls:
                continue
            ls = [l for l in ls if l is not True]
            terms.append(self.AND(ls, ("and", u, X, strict)) if ls else self.TRUE())
        return self.OR(terms, ("or", Y, X, strict)) if terms else self.FALSE()

    def TRUE(self):
        t = self.pool.id("TRUE")
        self.cl.append([t])
        return t

    def FALSE(self):
        return -self.TRUE()

    def below(self, z, X):
        """leaf z strictly below H_X."""
        return self.cmp(X, (z,), True)


def build(m, d, skip=()):
    S, LV, L = setup(m, d)
    e = Enc(len(LV))
    pairs = monotone_pairs(L)
    for idx, (s, t, i, j) in enumerate(pairs):
        if idx in skip:
            continue
        Y, Yp, X, Xp = set(L[s][j]), set(L[t][j]), set(L[s][i]), set(L[t][i])
        g1, g2 = e.cmp(Y, X, True), e.cmp(Yp, Xp, True)
        h1, h2 = e.cmp(Y, X, False), e.cmp(Yp, Xp, False)
        e.cl += [[-g1, g2], [g1, -g2], [-h1, h2], [h1, -h2]]
        for z in (Y - Yp) | (Xp - X):
            # tie (h1 and not g1) implies z below H_X
            e.cl.append([-h1, g1, e.below(z, X)])
    return S, LV, L, pairs, e


def solve(e):
    with Minisat22(bootstrap_with=e.cl) as sv:
        sat = sv.solve()
        model = sv.get_model() if sat else None
    return sat, model


def weak_order(e, model, n):
    pos = set(l for l in model if l > 0)
    score = [sum(1 for v in range(n) if v != u and e.ge(u, v) in pos) for u in range(n)]
    return score


if __name__ == "__main__":
    m, d = int(sys.argv[1]), int(sys.argv[2])
    S, LV, L, pairs, e = build(m, d)
    sat, model = solve(e)
    print(f"(m,d)=({m},{d}): leaves={len(LV)} words={len(S)} monotone pairs={len(pairs)} "
          f"clauses={len(e.cl)} -> {'SAT' if sat else 'UNSAT'}")
    if sat:
        print("  witness weak order (score = #leaves it is >=):", weak_order(e, model, len(LV)))
    if "--drop" in sys.argv:
        need = []
        for k in range(len(pairs)):
            _, _, _, _, e2 = build(m, d, skip=(k,))
            if solve(e2)[0]:
                need.append(k)
        print(f"  pairs whose removal makes it SAT: {[pairs[k] for k in need]}")
