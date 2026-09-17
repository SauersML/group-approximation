"""SAT search for finite non-left-orderability certificates.

Given a finite set B of nontrivial group elements closed under inverses, and a set of
triples (p, q, r) with p*q = r (all in B), a left order on the group restricts to a
choice P(g) in {True, False} for every g in B with P(g^-1) = not P(g) and
P(p) & P(q) => P(r).  If that CNF is UNSAT, the group is not left-orderable.
(Soundness only uses that the positive cone of a left order is a semigroup and that
exactly one of g, g^-1 is positive.)
"""
import sys
import time
from pysat.solvers import Solver


class CNFBuilder:
    def __init__(self, elements, inv):
        # elements: list of hashable nontrivial elements; inv: function
        self.var = {}
        nv = 0
        for g in elements:
            if g in self.var:
                continue
            gi = inv(g)
            assert gi != g, "torsion of order 2 in ball"
            nv += 1
            self.var[g] = nv
            self.var[gi] = -nv
        self.nv = nv
        self.clauses = set()

    def lit(self, g):
        return self.var.get(g)

    def add_triple(self, p, q, r):
        a, b, c = self.var.get(p), self.var.get(q), self.var.get(r)
        if a is None or b is None or c is None:
            return
        cl = tuple(sorted({-a, -b, c}))
        # skip tautologies
        if any(-x in cl for x in cl):
            return
        self.clauses.add(cl)

    def solve(self, name='cadical153', proof=None):
        t = time.time()
        with Solver(name=name, bootstrap_with=[list(c) for c in self.clauses]) as s:
            res = s.solve()
            model = s.get_model() if res else None
            core = None
        return res, model, time.time() - t


def write_dimacs(builder, path):
    with open(path, 'w') as f:
        f.write("p cnf %d %d\n" % (builder.nv, len(builder.clauses)))
        for c in builder.clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
