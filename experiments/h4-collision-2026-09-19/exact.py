# Exact (Q(sqrt5)) collision census for the W_X-fixed line L_X: bad rank-2 flats E (no L_X-wall through E),
# collision walls D_E = E + L_X, F-involvement, and a direct check that L_X is modular in A u D.
# usage: python3 exact.py H4 [H4Y H3 H3Y A4 A3]     (prints one block per type; pure integer/Fraction arithmetic)
import sys, itertools
from fractions import Fraction as Q
# field elements a + b*phi, phi^2 = phi + 1
def ad(x, y): return (x[0]+y[0], x[1]+y[1])
def sb(x, y): return (x[0]-y[0], x[1]-y[1])
def ml(x, y): a, b = x; c, d = y; return (a*c+b*d, a*d+b*c+b*d)
def iv(x):
    a, b = x; nm = a*a+a*b-b*b; return (Q(a+b)/nm, Q(-b)/nm)   # (a+b phi)(a+b-b phi) = a^2+ab-b^2
Z0, O1 = (0, 0), (1, 0)
def iz(x): return x[0] == 0 and x[1] == 0
def rank(rows):
    A = [list(r) for r in rows]; r = 0; nc = len(A[0])
    for c in range(nc):
        p = next((i for i in range(r, len(A)) if not iz(A[i][c])), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; ivp = iv(A[r][c])
        for i in range(len(A)):
            if i != r and not iz(A[i][c]):
                f = ml(A[i][c], ivp); A[i] = [sb(A[i][k], ml(f, A[r][k])) for k in range(nc)]
        r += 1
    return r
def kernel_line(rows, n):   # rows of rank n-1: return spanning vector of the kernel
    for t in range(n):      # try x_t = 1 with other free coords 0 by brute Cramer-free elimination
        A = [list(r) for r in rows] + [[O1 if k == t else Z0 for k in range(n)]]
        if rank(A) < n: continue
        # solve A x = e_last
        M = [A[i] + [O1 if i == len(A)-1 else Z0] for i in range(len(A))]
        r = 0; piv = []
        for c in range(n):
            p = next((i for i in range(r, len(M)) if not iz(M[i][c])), None)
            if p is None: continue
            M[r], M[p] = M[p], M[r]; ivp = iv(M[r][c]); M[r] = [ml(ivp, e) for e in M[r]]
            for i in range(len(M)):
                if i != r and not iz(M[i][c]):
                    f = M[i][c]; M[i] = [sb(M[i][k], ml(f, M[r][k])) for k in range(n+1)]
            piv.append(c); r += 1
        return [M[piv.index(c)][n] for c in range(n)]
def dot(u, v):
    s = Z0
    for a, b in zip(u, v): s = ad(s, ml(a, b))
    return s
def normalise(c):
    k = next(i for i, e in enumerate(c) if not iz(e)); f = iv(c[k]); return tuple(ml(f, e) for e in c)
TYPES = {'H4': (4, {(0, 1): 3, (1, 2): 3, (2, 3): 5}, [1, 2, 3], [0, 1, 2]),
         'H4Y': (4, {(0, 1): 3, (1, 2): 3, (2, 3): 5}, [0, 1, 2], [1, 2, 3]),
         'H3': (3, {(0, 1): 3, (1, 2): 5}, [1, 2], [0, 1]),
         'H3Y': (3, {(0, 1): 3, (1, 2): 5}, [0, 1], [1, 2]),
         'A4': (4, {(0, 1): 3, (1, 2): 3, (2, 3): 3}, [1, 2, 3], [0, 1, 2]),
         'A3': (3, {(0, 1): 3, (1, 2): 3}, [1, 2], [0, 1])}   # B_n needs sqrt2: see dwalls.py (float)
def setup(n, edges):
    G = [[(2, 0) if i == j else (0, 0) for j in range(n)] for i in range(n)]   # G = 2B, B(a_i,a_j)=-cos(pi/m)
    for (i, j), m in edges.items():
        G[i][j] = G[j][i] = (-1, 0) if m == 3 else (0, -1)
    return G
def roots(n, G):
    simple = [tuple(O1 if k == i else Z0 for k in range(n)) for i in range(n)]
    R = list(simple); seen = set(R)
    i = 0
    while i < len(R):
        r = R[i]; i += 1
        for s in range(n):
            c = dot([G[s][k] for k in range(n)], r)          # 2B(a_s, r)
            nr = tuple(sb(r[k], c) if k == s else r[k] for k in range(n))
            neg = tuple(sb(Z0, e) for e in nr)
            if nr not in seen and neg not in seen: seen.add(nr); R.append(nr)
    return R
from collections import Counter
def fmt(x):
    a, b = x; return f"{a}" if b == 0 else (f"{b}φ" if a == 0 else f"{a}+{b}φ")
def run(name, dump=None):
    n, edges, X, Y = TYPES[name]; G = setup(n, edges); R = roots(n, G)
    C = [tuple(dot(G[k], r) for k in range(n)) for r in R]           # wall of r = ker 2B(r, .)
    L = kernel_line([C[i] for i in X], n); LY = kernel_line([C[i] for i in Y], n)
    inX = {i for i in range(len(R)) if iz(dot(C[i], L))}; inY = {i for i in range(len(R)) if iz(dot(C[i], LY))}
    Fw = sorted(inY - inX); out = [i for i in range(len(R)) if i not in inX]
    flats = {}; owner = {}
    for i, j in itertools.combinations(range(len(R)), 2):
        if (i, j) in owner: continue
        mem = frozenset(k for k in range(len(R)) if rank([C[i], C[j], C[k]]) == 2)
        flats[mem] = 1
        for p in itertools.combinations(sorted(mem), 2): owner[p] = mem
    bad = [f for f in flats if not (f & inX)]
    Dkey = {}; Xkeys = {normalise(C[i]) for i in inX}
    for f in bad:
        i, j = sorted(f)[:2]
        c = tuple(sb(ml(C[i][k], dot(C[j], L)), ml(C[j][k], dot(C[i], L))) for k in range(n))
        Dkey.setdefault(normalise(c), []).append(f)
    assert not (set(Dkey) & Xkeys), "a collision wall coincides with an X-wall"
    walls_through_L = [C[i] for i in inX] + list(Dkey)
    for i, j in itertools.combinations(out, 2):          # modularity of L_X in A u D, checked pair by pair
        assert any(rank([C[i], C[j], w]) == 2 for w in walls_through_L), (i, j)
    sz = Counter(len(f) for f in bad); mult = Counter(len(v) for v in Dkey.values())
    fb = [f for f in bad if f & set(Fw)]
    print(f"{name}: roots {len(R)}, walls through L {len(inX)}, fibre punctures {len(out)}, F-walls {len(Fw)}")
    print(f"  rank-2 flats {len(flats)}; bad flats {len(bad)} by size {dict(sorted(sz.items()))};"
          f" bad pairs {sum(len(f)*(len(f)-1)//2 for f in bad)}")
    print(f"  collision walls {len(Dkey)}; #walls carrying m bad flats: {dict(sorted(mult.items()))}")
    print(f"  bad flats containing an F-wall {len(fb)} by size {dict(sorted(Counter(len(f) for f in fb).items()))};"
          f" by #F-walls {dict(Counter(len(f & set(Fw)) for f in fb))}")
    print(f"  per F-wall: " + ", ".join(f"{i}:{sum(1 for f in bad if i in f)}" for i in Fw))
    print("  modularity of L in A u D verified for all", len(out)*(len(out)-1)//2, "pairs")
    if dump:
        with open(dump, 'w') as fh:
            fh.write(f"# {name}: roots (simple-root coords, a+bφ); X={X} Y={Y}; F-walls={Fw}\n")
            for i, r in enumerate(R):
                tag = 'X' if i in inX else ('F' if i in Fw else '-')
                fh.write(f"r{i} {tag} [" + ", ".join(fmt(e) for e in r) + "]\n")
            fh.write("# bad flats: D-wall index, size, members (F-walls starred)\n")
            for d, (key, fl) in enumerate(sorted(Dkey.items(), key=lambda t: min(min(f) for f in t[1]))):
                for f in sorted(fl, key=min):
                    fh.write(f"D{d} {len(f)} " + " ".join(f"r{k}{'*' if k in Fw else ''}" for k in sorted(f)) + "\n")
if __name__ == '__main__':
    for nm in sys.argv[1:]:
        run(nm, dump=f"{nm}_flats.txt" if nm in ('H4', 'H3') else None)
