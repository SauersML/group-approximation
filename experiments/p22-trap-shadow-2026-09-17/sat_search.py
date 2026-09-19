#!/usr/bin/env python3
"""SAT search for permutation representations of the trap-relator group
Gamma (see trap_group.py) in which the head h = x_13(Q) acts nontrivially.

Usage: sat_search.py DEGREE [extra]

Each generator is an involutive permutation matrix of size DEGREE.  Every
word is built by chained products; the relations are asserted as equalities
of the product matrices; "h != 1" is a clause OR_i not h[i][i].
A model is re-verified by explicit permutation arithmetic before it is
reported.
"""
import sys

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153

import trap_group as TG


class Enc:
    def __init__(self, m):
        self.m = m
        self.pool = IDPool()
        self.cl = []
        self.mats = {}
        self.cache = {}

    def new_perm(self, key, involution=False):
        m = self.m
        X = [[self.pool.id((key, i, j)) for j in range(m)] for i in range(m)]
        for i in range(m):
            row = [X[i][j] for j in range(m)]
            col = [X[j][i] for j in range(m)]
            for lits in (row, col):
                enc = CardEnc.equals(lits=lits, bound=1, vpool=self.pool,
                                     encoding=EncType.seqcounter)
                self.cl.extend(enc.clauses)
        if involution:
            for i in range(m):
                for j in range(i + 1, m):
                    self.cl.append([-X[i][j], X[j][i]])
                    self.cl.append([X[i][j], -X[j][i]])
        return X

    def mul(self, A, B, key):
        """Z = A*B for permutation matrices (Z forced to be a permutation)."""
        m = self.m
        Z = self.new_perm(key)
        for i in range(m):
            for j in range(m):
                for k in range(m):
                    self.cl.append([-A[i][j], -B[j][k], Z[i][k]])
        return Z

    def word(self, names):
        names = tuple(names)
        if len(names) == 1:
            return self.mats[names[0]]
        if names in self.cache:
            return self.cache[names]
        P = self.word(names[:-1])
        Z = self.mul(P, self.mats[names[-1]], ("w",) + names)
        self.cache[names] = Z
        return Z

    def equal(self, A, B):
        m = self.m
        for i in range(m):
            for j in range(m):
                self.cl.append([-A[i][j], B[i][j]])
                self.cl.append([A[i][j], -B[i][j]])


def build(m, extra):
    E = Enc(m)
    for g in TG.GEN_NAMES:
        E.mats[g] = E.new_perm(("g", g), involution=True)
    for name, word in TG.DERIVED:
        E.mats[name] = E.word(word)
    rels = TG.TRAP_RELS + (TG.EXTRA_RELS if extra else [])
    for _, lhs, rhs in rels:
        E.equal(E.word(lhs), E.word(rhs))
    H = E.mats["h"]
    E.cl.append([-H[i][i] for i in range(m)])
    # symmetry breaking: h moves point 0
    E.cl.append([-H[0][0]])
    return E


def extract(E, model, m):
    s = set(v for v in model if v > 0)
    perms = {}
    for g in TG.GEN_NAMES:
        X = E.mats[g]
        p = [None] * m
        for i in range(m):
            for j in range(m):
                if X[i][j] in s:
                    p[i] = j
        perms[g] = tuple(p)
    return perms


# permutation arithmetic matching matrix products: (A*B)[i][k] = A[i][j]B[j][k]
# i.e. i -> A(i) = j -> B(j) = k, so compose left to right.
def pmul(p, q):
    return tuple(q[p[i]] for i in range(len(p)))


def pword(val, names):
    m = len(next(iter(val.values())))
    out = tuple(range(m))
    for g in names:
        out = pmul(out, val[g])
    return out


def verify(perms, extra):
    val = dict(perms)
    ident = tuple(range(len(perms["u"])))
    for g in TG.GEN_NAMES:
        assert pmul(val[g], val[g]) == ident, g
    for name, word in TG.DERIVED:
        val[name] = pword(val, word)
    rels = TG.TRAP_RELS + (TG.EXTRA_RELS if extra else [])
    for name, lhs, rhs in rels:
        assert pword(val, lhs) == pword(val, rhs), name
    assert val["h"] != ident
    return val


def main():
    m = int(sys.argv[1])
    extra = len(sys.argv) > 2 and sys.argv[2] == "extra"
    E = build(m, extra)
    with Cadical153(bootstrap_with=E.cl) as s:
        sat = s.solve()
        print("degree", m, "extra" if extra else "trap-only", "vars", E.pool.top,
              "clauses", len(E.cl), "SAT" if sat else "UNSAT")
        if sat:
            perms = extract(E, s.get_model(), m)
            val = verify(perms, extra)
            for g in TG.GEN_NAMES:
                print(" ", g, perms[g])
            print("  h", val["h"])


if __name__ == "__main__":
    main()
