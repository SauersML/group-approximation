# Is 1 in J (right ideal of F_p F_4)?  Search sum_i gen_i h_i = 1 with h_i supported in a ball.
# Generators: M^k(g), M^k(T g) for g in gens0(), |k| <= K, where M(h) = Rp phi^-2(h) = T^2 mod J.
import sys, time, itertools
from redJ import gens0, T, fmul, fphi, fadd
from fbc import red
import flint
def M(h, k):
    for _ in range(abs(k)):
        if k > 0: h = fmul({'Rp': 1}, fphi(h, -2))
        else: h = fphi(fmul({'Pr': 1}, h), 2)
    return h
def ball(R):
    L = 'pqrsPQRS'; out = ['']; layer = ['']
    for _ in range(R):
        new = []
        for w in layer:
            for c in L:
                if w and w[-1] == c.swapcase(): continue
                new.append(w + c)
        out += new; layer = new
    return out
def run(K, R, p, extra=()):
    S = gens0(); G = {}
    for name, g in S.items():
        for k in range(-K, K + 1):
            G[(name, k, 0)] = M(g, k); G[(name, k, 1)] = M(T(g), k)
    B = ball(R)
    cols = []
    for key, g in G.items():
        for w in B:
            col = {}
            for u, v in g.items():
                x = red(u + w); col[x] = (col.get(x, 0) + v) % p
            col = {x: v for x, v in col.items() if v}
            if col: cols.append(col)
    # peel: rows (words) touched by exactly one live column, with target 0, kill that column
    target = ''
    alive = set(range(len(cols)))
    rows = {}
    for j, col in enumerate(cols):
        for x in col: rows.setdefault(x, set()).add(j)
    stack = [x for x, s in rows.items() if len(s) == 1 and x != target]
    while stack:
        x = stack.pop()
        s = rows.get(x)
        if not s or len(s) != 1 or x == target: continue
        (j,) = s
        alive.discard(j)
        for y in cols[j]:
            rows[y].discard(j)
            if len(rows[y]) == 1 and y != target: stack.append(y)
    live_rows = sorted(x for x, s in rows.items() if s)
    if target not in live_rows:
        return len(cols), len(alive), len(live_rows), 'target dead'
    ridx = {x: i for i, x in enumerate(live_rows)}
    al = sorted(alive)
    A = flint.nmod_mat(len(live_rows), len(al) + 1, p)
    for jj, j in enumerate(al):
        for x, v in cols[j].items(): A[ridx[x], jj] = v
    A[ridx[target], len(al)] = 1
    r1 = A.rank()
    A2 = flint.nmod_mat(len(live_rows), len(al), p)
    for jj, j in enumerate(al):
        for x, v in cols[j].items(): A2[ridx[x], jj] = v
    r0 = A2.rank()
    return len(cols), len(al), len(live_rows), ('SOLVABLE' if r0 == r1 else 'no'), r0
if __name__ == '__main__':
    p = int(sys.argv[1])
    for spec in sys.argv[2:]:
        K, R = map(int, spec.split(':'))
        t0 = time.time()
        print('p', p, 'K', K, 'R', R, run(K, R, p), '%.1fs' % (time.time() - t0), flush=True)
