"""face_form_sat.py plus lex-leader symmetry breaking under the hyperoctahedral group.

The model of face_form_sat.py is invariant under the symmetry group of the cube
(coordinate permutations and reflections x_nu -> 1 - x_nu, 2^N N! elements, 48 for N = 3),
acting on cells and on labels.  For every non-identity group element g we add the
(truncated) lex-leader constraint  V <=_lex g(V),  where V is the vector of level bits
ge(c, t) in a fixed cell order.  Every orbit of models contains a lex-minimal one, which
satisfies all these constraints, so SAT/UNSAT is unchanged (sound symmetry breaking).
Truncation to the first `depth` positions keeps soundness.

Usage: python3 face_form_sat_sym.py N n [depth|0] [maxlev] [cap]
"""
import itertools, sys, json, time
from pysat.formula import IDPool
import face_form_sat as base


def group(N, L):
    for perm in itertools.permutations(range(N)):
        for flips in itertools.product((0, 1), repeat=N):
            if perm == tuple(range(N)) and not any(flips):
                continue
            def g(c, perm=perm, flips=flips):
                d = [0] * N
                for i in range(N):
                    v = c[perm[i]]
                    d[i] = L - 1 - v if flips[i] else v
                return tuple(d)
            yield g


def lex_leq(S, pool, X, Y, tag):
    """Encode X <=_lex Y for literal lists X, Y (standard chain encoding)."""
    # e_i : X[0..i-1] == Y[0..i-1]
    prev = None
    for i, (x, y) in enumerate(zip(X, Y)):
        if x == y:
            continue
        # if prefix equal then x <= y
        cond = [] if prev is None else [-prev]
        S.add_clause(cond + [-x, y])
        e = pool.id(('lexeq', tag, i))
        # e -> prefix equal and x == y
        if prev is not None:
            S.add_clause([-e, prev])
        S.add_clause([-e, -x, y]); S.add_clause([-e, x, -y])
        # prefix equal and x == y -> e  (needed so later constraints bind)
        S.add_clause(cond + [x, y, e]); S.add_clause(cond + [-x, -y, e])
        prev = e


def run(N, n, depth=None, maxlev=None, cap=None):
    L = 2 * n + 1
    if maxlev is None:
        maxlev = N - 1

    def extra(S, pool, cells, ge, lab):
        # order: level bits, cells by distance from centre first (more constraining)
        centre = (L - 1) / 2
        order = sorted(cells, key=lambda c: (sum(abs(x - centre) for x in c), c))
        keys = [(c, t) for c in order for t in range(maxlev, 0, -1)]
        if depth:
            keys = keys[:depth]
        X = [ge(c, t) for c, t in keys]
        for k, g in enumerate(group(N, L)):
            Y = [ge(g(c), t) for c, t in keys]
            lex_leq(S, pool, X, Y, k)

    return base.run(N, n, maxlev, extra=extra, cap=cap)


if __name__ == '__main__':
    N = int(sys.argv[1]); n = int(sys.argv[2])
    depth = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '0' else None
    maxlev = int(sys.argv[4]) if len(sys.argv) > 4 else None
    cap = int(sys.argv[5]) if len(sys.argv) > 5 else None
    ok, dt, sol = run(N, n, depth, maxlev, cap)
    print(json.dumps({'N': N, 'n': n, 'sym': 'lex-leader, 2^N N! - 1 elements', 'depth': depth, 'maxlev': maxlev, 'cap': cap,
                      'cells': (2 * n + 1) ** N, 'result': 'SAT' if ok else 'UNSAT',
                      'seconds': round(dt, 2)}), flush=True)
    if ok:
        with open(f'sol_sym_N{N}_n{n}.json', 'w') as f:
            json.dump(sol, f)
