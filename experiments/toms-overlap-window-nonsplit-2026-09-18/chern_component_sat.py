"""Chern-component model of a box of N ideal two-wall overlap windows.

A target Q whose rank is constant on each vertex slice {s} x Y is described by
delta(s) = U - rank Q(s) >= 0, an upper semicontinuous integer function on the box
S = prod_nu I_nu (rank is lower semicontinuous).  On every connected component
Omega of a level set {delta = t} the support of Q is a vector bundle, so its total
Chern class is constant on Omega and divisible, node by node, by the lcm of the
pushforward's leaf factors over Omega (coprime divisibility, Part 1 of
toms-overlap-window-drops-need-not-coincide-proof).  This gives the necessary
condition

    delta(Omega) + sum_nu e(pi_nu Omega) <= N,

with e(J) = #walls strictly crossed by J, minus 1 if J is a single wall point.

The box is discretised as a product cell complex (each chamber split into m open
intervals and m-1 interior points).  delta is constant on cells, usc means
delta(face) >= delta(coface); components are joined along face relations.
SAT = a delta of the given maximal depth exists in the model (a candidate
staggering to test for realisability); UNSAT = excluded in the model at this
resolution.
"""
import itertools, sys, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

ZONES = ['A', 'w1', 'B', 'w2', 'C']


def coord_cells(m):
    cells = [(0, 'A')]  # (dim, zone); starts with endpoint 0
    for zone, wall in (('A', 'w1'), ('B', 'w2'), ('C', None)):
        for i in range(m):
            cells.append((1, zone))
            if i < m - 1:
                cells.append((0, zone))
        cells.append((0, wall if wall else 'C'))
    return cells


def run(N, depth, m=2, budget=None, lam=1, span_mode=False):
    if budget is None:
        budget = N
    cc = coord_cells(m)
    L = len(cc)
    pool = IDPool()
    cells = list(itertools.product(range(L), repeat=N))
    g = lambda c, t: pool.id(('g', c, t))
    z = lambda c, nu, Z: pool.id(('z', c, nu, Z))
    cl = []
    for c in cells:
        for t in range(2, depth + 1):
            cl.append([-g(c, t), g(c, t - 1)])
        for nu in range(N):
            cl.append([z(c, nu, cc[c[nu]][1])])
    # codim-1 face relations: tau (open in coord nu) -> faces sigma
    for tau in cells:
        for nu in range(N):
            i = tau[nu]
            if cc[i][0] != 1:
                continue
            for j in (i - 1, i + 1):
                sig = tau[:nu] + (j,) + tau[nu + 1:]
                for t in range(1, depth + 1):
                    cl.append([-g(tau, t), g(sig, t)])  # usc
                ds = []
                for t in range(1, depth + 1):
                    d = pool.id(('d', tau, sig, t))
                    cl.append([-d, g(sig, t)])
                    cl.append([-d, -g(tau, t)])
                    ds.append(d)
                for mu in range(N):
                    for Z in ZONES:
                        cl.append([-z(tau, mu, Z), z(sig, mu, Z)] + ds)
                        cl.append([-z(sig, mu, Z), z(tau, mu, Z)] + ds)
    for c in cells:
        lits = [g(c, t) for t in range(1, depth + 1) for _ in range(lam)]
        for nu in range(N):
            b1, b2, b3 = (pool.id(('b', c, nu, k)) for k in (1, 2, 3))
            for Z in ('A', 'B', 'C'):
                cl.append([-z(c, nu, Z), b1])
            cl.append([-z(c, nu, 'w1'), -z(c, nu, 'w2'), b1])
            for X, Y in (('A', 'B'), ('B', 'C'), ('A', 'C')):
                cl.append([-z(c, nu, X), -z(c, nu, Y), b2])
            cl.append([-z(c, nu, 'A'), -z(c, nu, 'C'), b3])
            lits += [b3] if span_mode else [b1, b2, b3]
        enc = CardEnc.atmost(lits=lits, bound=(N - 1) if span_mode else budget + N, vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
    with Cadical153(bootstrap_with=cl) as s:
        ok = s.solve()
        sol = None
        if ok:
            mdl = set(x for x in s.get_model() if x > 0)
            sol = {c: sum(1 for t in range(1, depth + 1) if g(c, t) in mdl)
                   for c in cells}
    return ok, sol, cc


if __name__ == '__main__':
    N, depth, m = (int(a) for a in sys.argv[1:4])
    ok, sol, cc = run(N, depth, m)
    print(json.dumps({'N': N, 'depth': depth, 'm': m, 'sat': ok}))
    if ok and N <= 2:
        L = len(cc)
        for i in range(L):
            print(''.join(str(sol[(i, j)]) for j in range(L)))
