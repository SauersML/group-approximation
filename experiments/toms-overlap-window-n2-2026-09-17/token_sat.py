"""Token model of the N=2 overlap-window box.

A rank-(m or m-1) target is modelled by a map from the box S = I_1 x I_2 to the
complex |K|: vertices are 6-token configurations X in bins (a1,b1,a2,b2,o_1..o_O)
(relative counts of L_(1,+), L_(1,-), L_(2,+), L_(2,-), other lines, over the
common part of rank m-6), simplices are the stars {W0 + e_i} of 5-token
configurations W0 ("one line in transit", rank >= m-1 everywhere).
Containment of the pushforward = floor constraint: on a closed region, every
simplex used has W0 >= req (componentwise, on the node bins).

Regions along each node coordinate (t grid units each), with node requirements
(a,b):  A (0,2) | g1 (0,1) | B (1,1) | g2 (1,0) | C (2,0).
With gaps=False the walls are lines (closed chambers meet directly).

A simplicial map on a fine triangulation exists iff (up to subdivision) a
continuous staggered map exists.  SAT = staggering possible in the token model.
"""
import itertools, sys, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def configs(total, nb):
    out = []
    for c in itertools.combinations_with_replacement(range(nb), total):
        v = [0]*nb
        for i in c: v[i] += 1
        out.append(tuple(v))
    return out

REQ = {'A': (0, 2), 'g1': (0, 1), 'B': (1, 1), 'g2': (1, 0), 'C': (2, 0)}

def run(t=1, O=1, gaps=True, tokens=6, reqs=REQ, pattern=None):
    nb = 4 + O
    V6 = configs(tokens, nb)
    V5 = configs(tokens - 1, nb)
    if pattern is None:
        pattern = ['A', 'g1', 'B', 'g2', 'C'] if gaps else ['A', 'B', 'C']
    regs = [r for r in pattern for _ in range(t)]
    n = len(regs)  # intervals; vertices 0..n
    def req2(r1, r2):
        return reqs[r1] + reqs[r2]
    def ge(X, rq):
        return all(X[i] >= rq[i] for i in range(4))
    pool = IDPool()
    cl = []
    def adj(i):
        return [regs[k] for k in (i - 1, i) if 0 <= k < n]
    xv = {}
    for i in range(n + 1):
        for j in range(n + 1):
            dom = [c for c in V6 if all(ge(c, req2(r1, r2)) for r1 in adj(i) for r2 in adj(j))]
            if not dom:
                return 'UNSAT(empty-domain)', None
            xv[(i, j)] = {c: pool.id(('x', i, j, c)) for c in dom}
            lits = list(xv[(i, j)].values())
            cl.append(lits)
            enc = CardEnc.atmost(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter)
            cl.extend(enc.clauses)
    tris = []
    for i in range(n):
        for j in range(n):
            rq = req2(regs[i], regs[j])
            tris.append(((i, j), (i + 1, j), (i + 1, j + 1), rq))
            tris.append(((i, j), (i, j + 1), (i + 1, j + 1), rq))
    for k, (p, q, r, rq) in enumerate(tris):
        sig = []
        for W in V5:
            if ge(W, rq):
                verts = [tuple(W[a] + (1 if a == b else 0) for a in range(nb)) for b in range(nb)]
                sig.append(('W', W, verts))
        for X in V6:
            if ge(X, rq):
                sig.append(('X', X, [X]))
        ys = []
        for s in sig:
            y = pool.id(('y', k, s[0], s[1]))
            ys.append(y)
            for v in (p, q, r):
                cl.append([-y] + [xv[v][c] for c in s[2] if c in xv[v]])
        cl.append(ys)
    solver = Cadical153(bootstrap_with=cl)
    ok = solver.solve()
    sol = None
    if ok:
        model = set(l for l in solver.get_model() if l > 0)
        sol = {}
        for (i, j), d in xv.items():
            for c, lit in d.items():
                if lit in model:
                    sol[(i, j)] = c
    return ('SAT' if ok else 'UNSAT'), sol

if __name__ == '__main__':
    res = {}
    for gaps in (False, True):
        for O in (1, 2):
            for t in (1, 2, 3):
                st, sol = run(t=t, O=O, gaps=gaps)
                key = f"gaps={gaps},O={O},t={t}"
                res[key] = st
                print(key, st, flush=True)
    json.dump(res, open(sys.argv[1] if len(sys.argv) > 1 else 'token_sat_results.json', 'w'), indent=1)
