"""SAT search for brick codings of the Robertson-Steger 2-graph in dimension m.

A brick coding assigns to each edge e a brick code phi(e) = (w_1,...,w_m), w_j binary
words, such that
  (C1) for each vertex a and colour i the codes of the edges a -> * of colour i are the
       codes of a partition of the Cantor cube C^m into dyadic bricks;
  (C2) every square (e f = f' e') satisfies phi_j(e) phi_j(f) = phi_j(f') phi_j(e') for all j.
(Nondegeneracy is not imposed, so UNSAT is an obstruction to every brick coding.)
Here each vertex emits 4 edges of each colour, so every brick has volume >= 1/8 and
total length <= 3: the code domain below is complete and the search is exhaustive in m.
"""
import itertools, sys, json, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
import rs2graph


def words(n):
    return ["".join(p) for p in itertools.product("01", repeat=n)]


def codes(m, tmax):
    out = []
    for lens in itertools.product(range(tmax + 1), repeat=m):
        if sum(lens) <= tmax:
            for ws in itertools.product(*[words(l) for l in lens]):
                out.append(tuple(ws))
    return out


def intersect(c, d):
    return all(a.startswith(b) or b.startswith(a) for a, b in zip(c, d))


def vol8(c):
    return 2 ** (3 - sum(len(w) for w in c))


def partitions4(m):
    """unordered 4-brick partitions of C^m, as sorted tuples"""
    C = codes(m, 3)
    res = set()
    byvol = {}
    for c in C:
        byvol.setdefault(vol8(c), []).append(c)
    # volumes {2,2,2,2} (length 2 each) or {4,2,1,1} (lengths 1,2,3,3)
    for combo in itertools.combinations(byvol[2], 4):
        if all(not intersect(a, b) for a, b in itertools.combinations(combo, 2)):
            res.add(tuple(sorted(combo)))
    for a in byvol[4]:
        for b in byvol[2]:
            if intersect(a, b):
                continue
            for c, d in itertools.combinations(byvol[1], 2):
                combo = (a, b, c, d)
                if all(not intersect(x, y) for x, y in itertools.combinations(combo, 2)):
                    res.add(tuple(sorted(combo)))
    return sorted(res)


def concat(c, d):
    return tuple(a + b for a, b in zip(c, d))


def solve(T, m, extra=None, verbose=True, uniform=False, solver=Cadical153):
    """uniform=True restricts to codes of total length 2 (all edges): by the
    cohomological argument in README (H^1 of the square complex is spanned by the
    degree cocycles, M_1, M_2 primitive with row sums 4, Kraft equality) every brick
    coding of these 2-graphs has total length 2 on every edge, so this loses nothing."""
    tiles, E1, E2, squares = rs2graph.build(T)
    nV = len(tiles)
    C = codes(m, 3)
    parts = partitions4(m)
    if uniform:
        C = [c for c in C if sum(map(len, c)) == 2]
        parts = [p for p in parts if all(sum(map(len, c)) == 2 for c in p)]
    pool = IDPool()
    X = lambda col, e, c: pool.id(("X", col, e, c))
    clauses = []
    edges = {1: E1, 2: E2}
    for col in (1, 2):
        out = {}
        for i, (a, b) in enumerate(edges[col]):
            out.setdefault(a, []).append(i)
        for a in range(nV):
            es = out[a]
            # choose an ordered assignment of a partition to the 4 edges
            opts = []
            for p in parts:
                for perm in set(itertools.permutations(p)):
                    v = pool.id(("P", col, a, perm))
                    opts.append(v)
                    for e, c in zip(es, perm):
                        clauses.append([-v, X(col, e, c)])
            clauses.append(opts)
        for i in range(len(edges[col])):
            lits = [X(col, i, c) for c in C]
            clauses += CardEnc.atmost(lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    for s, (e, f, f2, e2) in enumerate(squares):
        Z = {}
        for c in C:
            for d in C:
                pr = concat(c, d)
                z = Z.setdefault(pr, pool.id(("Z", s, pr)))
                clauses.append([-X(1, e, c), -X(2, f, d), z])
                # second factorisation: phi(f2) phi(e2)
                clauses.append([-X(2, f2, c), -X(1, e2, d), z])
        clauses += CardEnc.atmost(list(Z.values()), bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    if extra:
        clauses += extra(pool, X, E1, E2, C)
    if verbose:
        print(f"m={m}: {len(C)} codes, {len(parts)} partitions, {pool.top} vars, {len(clauses)} clauses", flush=True)
    t = time.time()
    with solver(bootstrap_with=clauses) as S:
        ok = S.solve()
        model = set(x for x in S.get_model() if x > 0) if ok else None
    if verbose:
        print(f"m={m} [{solver.__name__}]: {'SAT' if ok else 'UNSAT'} in {time.time()-t:.1f}s", flush=True)
    if not ok:
        return None
    phi = {}
    for col in (1, 2):
        for i in range(len(edges[col])):
            cs = [c for c in C if X(col, i, c) in model]
            phi[(col, i)] = cs[0]
    return tiles, E1, E2, squares, phi


if __name__ == "__main__":
    ex = json.load(open("tp_q2.json"))["examples"]
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    uni = len(sys.argv) > 3 and sys.argv[3] == "uniform"
    r = solve(ex[k][1], m, uniform=uni)
    if r:
        tiles, E1, E2, squares, phi = r
        json.dump({str(k): v for k, v in phi.items()}, open(f"coding_T{k}_m{m}.json", "w"))
