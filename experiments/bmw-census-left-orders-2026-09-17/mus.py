# Extract a small unsatisfiable core (deletion-based MUS over the triple clauses) for one complex.
import sys, json
from pysat.solvers import Cadical153
from lo_census import VH, ball, lo_sat, load
def core(G, R, sh):
    idx, els = ball(G, R)
    nb, nk, cls = lo_sat(G, R, sh)
    pair = [c for c in cls if len(c) == 2 and c[0] > 0]  # p_g or p_g^-1
    rest = [c for c in cls if not (len(c) == 2 and c[0] > 0) and not (len(c) == 2 and c[0] < 0 and c[1] < 0 and False)]
    hard = [c for c in cls if len(c) == 2 and ((c[0] > 0 and c[1] > 0) )] + \
           [c for c in cls if len(c) == 2 and c[0] < 0 and c[1] < 0 and all(abs(x) for x in c)]
    soft = [c for c in cls if len(c) == 3]
    # selectors
    top = max(abs(x) for c in cls for x in c)
    with Cadical153(bootstrap_with=hard) as s:
        sel = []
        for k, c in enumerate(soft):
            v = top + 1 + k; sel.append(v); s.add_clause(c + [-v])
        assert not s.solve(assumptions=sel)
        cur = list(s.get_core())
        changed = True
        while changed:
            changed = False
            for v in list(cur):
                trial = [x for x in cur if x != v]
                if not s.solve(assumptions=trial):
                    cur = list(s.get_core()); changed = True; break
    trip = [soft[v - top - 1] for v in cur]
    return els, trip
def name(G, g):
    v, h = g
    return ''.join('xyzw'[c] for c in v) + ''.join('abcd'[c] for c in h)
if __name__ == "__main__":
    path, i, R = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    sh = int(sys.argv[4]) if len(sys.argv) > 4 else None
    for j, G in load(path):
        if j != i: continue
        els, trip = core(G, R, sh)
        print('triples', len(trip))
        for c in trip:
            a, b, k = -c[0], -c[1], c[2]
            print(name(G, els[a]), '*', name(G, els[b]), '=', name(G, els[k]))
