"""Exact SAT search for face counterexamples of the spanning principle (S).

A face counterexample is an upper semicontinuous delta : I^N -> Z_{>=0} such that every
level component (component of some {delta = t}) fails at least t + 1 coordinates, where a
set fails nu if it misses the face x_nu = 0 or the face x_nu = 1.  The face form F(N) says
none exists.  At max delta <= 2 it is equivalent to the relative Hex statement R1(3)
(toms-level-two-spanning-reduces-to-relative-hex).  In dimension N a level-t component
can fail at most N coordinates, so t <= N - 1 and the search is complete in the level range.

Model.  The product cell complex with n open intervals per coordinate (2n + 1 cells per
coordinate: n + 1 vertices, n open edges).  delta is constant on open cells; usc means
delta(face) >= delta(coface).  Two cells in a face relation with equal delta lie in the same
level component, and codimension-one relations generate these (usc forces every
intermediate cell to the same level).

Encoding (local, no connectivity variables).  Each cell carries labels l[nu, s].
- l[nu, -] means "my component misses x_nu = 1": forbidden on cells of that face.
- l[nu, +] means "my component misses x_nu = 0": forbidden on cells of that face.
- Labels are equal across every codimension-one face relation of equal level, so they are
  constant on components.
- sum_nu (l[nu,-] or l[nu,+]) >= delta + 1.
A model is exactly a cell-constant face counterexample (labels constant on a component
certify that the component misses the labelled faces), and conversely every cell-constant
face counterexample yields a model (label each component by its missed faces).
SAT is therefore a genuine counterexample to F(N); UNSAT excludes all counterexamples
that are constant on the cells of this complex.
"""
import itertools, sys, json, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def run(N, n, maxlev=None, extra=None, cap=None, keep=None):
    if maxlev is None:
        maxlev = N - 1
    L = 2 * n + 1
    cells = list(itertools.product(range(L), repeat=N))
    if keep is not None:
        cells = [c for c in cells if keep(c, L)]
    cellset = set(cells)
    pool = IDPool()
    # ge[c][t] : delta(c) >= t, t = 1..maxlev
    ge = lambda c, t: pool.id(('ge', c, t))
    lab = lambda c, nu, s: pool.id(('l', c, nu, s))
    fl = lambda c, nu: pool.id(('f', c, nu))
    S = Cadical153()
    for c in cells:
        for t in range(2, maxlev + 1):
            S.add_clause([-ge(c, t), ge(c, t - 1)])
        for nu in range(N):
            # faces
            if c[nu] == L - 1:
                S.add_clause([-lab(c, nu, 0)])
            if c[nu] == 0:
                S.add_clause([-lab(c, nu, 1)])
            # f = l- or l+
            S.add_clause([-fl(c, nu), lab(c, nu, 0), lab(c, nu, 1)])
        fs = [fl(c, nu) for nu in range(N)]
        # sum f >= 1 always; >= t+1 when delta >= t
        S.add_clause(fs)
        for t in range(1, maxlev + 1):
            # ge(c,t) -> at least t+1 of fs
            enc = CardEnc.atleast(lits=fs, bound=min(t + 1, cap if cap else t + 1), vpool=pool, encoding=EncType.seqcounter)
            for cl in enc.clauses:
                S.add_clause(cl + [-ge(c, t)])
    # face relations: c (lower dim, a vertex index in coord nu) is a face of d (edge index)
    for d in cells:
        for nu in range(N):
            if d[nu] % 2 == 1:  # open edge in coord nu
                for off in (-1, 1):
                    c = list(d); c[nu] += off; c = tuple(c)
                    if c not in cellset:
                        continue
                    # usc: delta(c) >= delta(d)
                    for t in range(1, maxlev + 1):
                        S.add_clause([-ge(d, t), ge(c, t)])
                    # equal level -> equal labels.  eq holds iff for all t ge(c,t) == ge(d,t);
                    # given usc, eq fails iff some t with ge(c,t) and not ge(d,t).
                    # So: for each t: (not ge(c,t) or ge(d,t)) for all t ... encode
                    # neq -> exists t: ge(c,t) & -ge(d,t).  Label equality under eq:
                    e = pool.id(('eq', c, d))
                    # -e -> OR_t (ge(c,t) & -ge(d,t)); use aux x_t
                    xs = []
                    for t in range(1, maxlev + 1):
                        x = pool.id(('x', c, d, t)); xs.append(x)
                        S.add_clause([-x, ge(c, t)]); S.add_clause([-x, -ge(d, t)])
                    S.add_clause([e] + xs)
                    for nu2 in range(N):
                        for s in (0, 1):
                            S.add_clause([-e, -lab(c, nu2, s), lab(d, nu2, s)])
                            S.add_clause([-e, lab(c, nu2, s), -lab(d, nu2, s)])
    if extra:
        extra(S, pool, cells, ge, lab)
    t0 = time.time()
    ok = S.solve()
    dt = time.time() - t0
    sol = None
    if ok:
        m = set(l for l in S.get_model() if l > 0)
        sol = {str(c): sum(1 for t in range(1, maxlev + 1) if ge(c, t) in m) for c in cells}
    return ok, dt, sol


if __name__ == '__main__':
    N = int(sys.argv[1]); n = int(sys.argv[2])
    maxlev = int(sys.argv[3]) if len(sys.argv) > 3 else None
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else None
    ok, dt, sol = run(N, n, maxlev, cap=cap)
    print(json.dumps({'N': N, 'n': n, 'maxlev': maxlev if maxlev is not None else N - 1,
                      'cap': cap, 'cells': (2 * n + 1) ** N, 'result': 'SAT' if ok else 'UNSAT',
                      'seconds': round(dt, 2)}))
    if ok:
        with open(f'sol_N{N}_n{n}.json', 'w') as f:
            json.dump(sol, f)
