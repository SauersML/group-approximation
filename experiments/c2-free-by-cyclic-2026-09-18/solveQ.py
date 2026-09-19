# Solve the pruned K=0 system over Q (exact) and report the solution.
import sys, flint
from redJ import gens0, T
from searchJ import ball
from fbc import red
def build(R):
    S = gens0(); G = {}
    for name, g in S.items():
        G[(name, 0)] = g; G[(name, 1)] = T(g)
    cols = []; keys = []
    for key, g in G.items():
        for w in ball(R):
            col = {}
            for u, v in g.items():
                x = red(u + w); col[x] = col.get(x, 0) + v
            col = {x: v for x, v in col.items() if v}
            if col: cols.append(col); keys.append((key, w))
    target = ''
    rows = {}
    for j, col in enumerate(cols):
        for x in col: rows.setdefault(x, set()).add(j)
    alive = set(range(len(cols)))
    stack = [x for x, s in rows.items() if len(s) == 1 and x != target]
    while stack:
        x = stack.pop(); s = rows.get(x)
        if not s or len(s) != 1 or x == target: continue
        (j,) = s; alive.discard(j)
        for y in cols[j]:
            rows[y].discard(j)
            if len(rows[y]) == 1 and y != target: stack.append(y)
    live = sorted(x for x, s in rows.items() if s)
    return G, cols, keys, sorted(alive), live
def solve(R):
    G, cols, keys, al, live = build(R)
    ridx = {x: i for i, x in enumerate(live)}
    A = flint.fmpq_mat(len(live), len(al)); b = flint.fmpq_mat(len(live), 1)
    for jj, j in enumerate(al):
        for x, v in cols[j].items(): A[ridx[x], jj] = v
    b[ridx[''], 0] = 1
    At = A.transpose(); N = At * A
    print('rank', N.rank(), 'cols', len(al))
    x = N.solve(At * b)
    ok = (A * x == b)
    print('exact solution', ok)
    sol = [(keys[j], x[jj, 0]) for jj, j in enumerate(al) if x[jj, 0] != 0]
    return G, sol, ok
if __name__ == '__main__':
    G, sol, ok = solve(int(sys.argv[1]))
    print(len(sol), 'nonzero'); print(sorted(set(str(v) for _, v in sol)))
