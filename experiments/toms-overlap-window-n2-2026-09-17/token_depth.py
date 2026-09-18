"""Split (token) model of an N-node overlap-window box: minimal forced depth.

Bins: (a_nu, b_nu) for nu = 1..N (extra copies of L_(nu,+), L_(nu,-) over the
common part p* L_+ + q* L_- of each node, shifted so that the chamber needs are
A:(0,2)  B:(1,1)  C:(2,0)), plus one bin 'o' for any other lines.  The upper
band leaves T = 3N tokens (room three per node).  Along each node coordinate the
regions are A | g1 | B | g2 | C, with gap needs g1:(0,1), g2:(1,0) (the
pushforward's lower wall value; a positive-width gap models the fading
eigenvalue that lower semicontinuity allows at a wall).

A target with rank >= U - d everywhere is modelled by a continuous map from the
box into |K_d| = {v >= 0 : sum v = T, sum floor(v) >= T - d}, with floor(v) >= need
on each closed region.  On a Kuhn triangulation (t grid units per region) a
simplicial map exists iff, for each grid simplex sigma, there is an integer W
(the floor) with W >= need(sigma), sum W >= T - d, and W <= X_v <= W + 1 for
every vertex v of sigma.  Encoded in unary (order) encoding for SAT.

SAT at depth d: the split model staggers the drops so that no point loses more
than d ranks.  UNSAT: every split target drops by at least d + 1 somewhere.
"""
import itertools, sys, json, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

NEED = {'A': (0, 2), 'g1': (0, 1), 'B': (1, 1), 'g2': (1, 0), 'C': (2, 0)}

def solve(N, d, t=1, gaps=True, cap=4, tokens=None, ocap=None):
    T = 3 * N if tokens is None else tokens
    pattern = ['A', 'g1', 'B', 'g2', 'C'] if gaps else ['A', 'B', 'C']
    regs = [r for r in pattern for _ in range(t)]
    n = len(regs)
    nbins = 2 * N + 1
    caps = [cap] * (2 * N) + [T if ocap is None else ocap]
    pool = IDPool()
    cl = []
    def unary(tag):
        # bits[k] <-> value >= k+1 ; monotone
        bits = [[pool.id((tag, i, k)) for k in range(caps[i])] for i in range(nbins)]
        for i in range(nbins):
            for k in range(caps[i] - 1):
                cl.append([-bits[i][k + 1], bits[i][k]])
        return bits
    X = {}
    for v in itertools.product(range(n + 1), repeat=N):
        bits = unary(('x', v))
        X[v] = bits
        flat = [b for row in bits for b in row]
        enc = CardEnc.equals(lits=flat, bound=T, vpool=pool, encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
    nsimp = 0
    for cube in itertools.product(range(n), repeat=N):
        need = []
        for nu in range(N):
            need += list(NEED[regs[cube[nu]]])
        need.append(0)
        for perm in itertools.permutations(range(N)):
            verts = [tuple(cube)]
            cur = list(cube)
            for p in perm:
                cur[p] += 1
                verts.append(tuple(cur))
            W = unary(('w', cube, perm))
            nsimp += 1
            for i in range(nbins):
                for k in range(need[i]):
                    cl.append([W[i][k]])  # W_i >= need_i
                for v in verts:
                    xb = X[v][i]
                    for k in range(caps[i]):
                        cl.append([-W[i][k], xb[k]])          # W_i >= k+1 -> X_i >= k+1
                        if k + 1 < caps[i]:
                            cl.append([-xb[k + 1], W[i][k]])  # X_i >= k+2 -> W_i >= k+1
                    # X_i >= 1 -> W_i >= 0 trivially
            flat = [b for row in W for b in row]
            enc = CardEnc.atleast(lits=flat, bound=T - d, vpool=pool, encoding=EncType.seqcounter)
            cl.extend(enc.clauses)
    s = Cadical153(bootstrap_with=cl)
    t0 = time.time()
    ok = s.solve()
    dt = time.time() - t0
    sol = None
    if ok:
        m = set(l for l in s.get_model() if l > 0)
        sol = {v: tuple(sum(1 for b in row if b in m) for row in bits) for v, bits in X.items()}
    return ok, sol, dict(vars=pool.top, clauses=len(cl), simplices=nsimp, secs=round(dt, 2))

if __name__ == '__main__':
    N = int(sys.argv[1]); d = int(sys.argv[2]); t = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    gaps = (sys.argv[4] != 'nogaps') if len(sys.argv) > 4 else True
    ok, sol, info = solve(N, d, t=t, gaps=gaps)
    print(json.dumps(dict(N=N, d=d, t=t, gaps=gaps, result='SAT' if ok else 'UNSAT', **info)))
    if ok and len(sys.argv) > 5:
        json.dump({str(k): v for k, v in sol.items()}, open(sys.argv[5], 'w'))
