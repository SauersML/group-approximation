"""(RI_{L_j}) in the case the target needs: X of finite index in L_{j+1}.

X = ker(L_{j+1} -> G) for small G (or X = L_{j+1}); J = <X, g>; H = J cap L_j.
Lower bound for rk(H : X): the largest d(image) over homs H -> S3 that kill
X (d = 2 iff the image is S3), and the F_2/F_3 cokernel dims of
H_1(X) -> H_1(H).  A value > 1 = rk(J : X) is a violation of (RI_{L_j}).
"""
import itertools
import random
import sys
from stall import fold_graph, member, rank, basis, coords, intersect, L, red
from cover import kernel_graph
from searchB import regular, closure, GROUPS, words, compose

S3 = GROUPS['S3']
S3inv = {p: tuple(sorted(range(3), key=lambda i: p[i])) for p in S3}


def rel_image(rel, assign):
    cur = (0, 1, 2)
    for i, e in rel:
        p = assign[i] if e > 0 else S3inv[assign[i]]
        cur = compose(cur, p)
    return cur


def best_S3(r, rels, cap=None):
    """max d(image) over homs F_r -> S3 killing rels, by backtracking."""
    need = [max((i for i, _ in rel), default=-1) for rel in rels]
    by_last = {}
    for rel, m in zip(rels, need):
        by_last.setdefault(m, []).append(rel)
    if any(not rel for rel in by_last.get(-1, [])):
        pass
    best = [0]
    assign = [None] * r

    def rec(i):
        if i == r:
            img = len(closure(list(assign)))
            d = 0 if img == 1 else (2 if img == 6 else 1)
            best[0] = max(best[0], d)
            return best[0] == 2
        for p in S3:
            assign[i] = p
            if all(rel_image(rel, assign) == (0, 1, 2)
                   for rel in by_last.get(i, [])):
                if rec(i + 1):
                    return True
        assign[i] = None
        return False
    rec(0)
    return best[0]


def rank_mod_p(rows, p, ncols):
    m = [[x % p for x in row] for row in rows]
    rk, col = 0, 0
    for col in range(ncols):
        piv = next((i for i in range(rk, len(m)) if m[i][col]), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        iv = pow(m[rk][col], p - 2, p)
        m[rk] = [(x * iv) % p for x in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][col]:
                f = m[i][col]
                m[i] = [(x - f * y) % p for x, y in zip(m[i], m[rk])]
        rk += 1
    return rk


def run(j, gname, maxlen, nrho, seed):
    rng = random.Random(seed)
    GA = fold_graph(L(j + 1))
    GB = fold_graph(L(j))
    Xs = [('X=L_%d' % (j + 1), GA)]
    if gname != 'none':
        elts = GROUPS[gname]
        for _ in range(nrho):
            while True:
                ps = [rng.choice(elts) for _ in range(2)]
                if len(closure(ps)) == len(elts):
                    break
            Xs.append((str(ps), kernel_graph(GA, [regular(elts, p) for p in ps])))
    viol = tested = skipped = 0
    hist = {}
    for name, GX in Xs:
        _, xg, _ = basis(GX)
        for g in words(maxlen):
            if member(GX, g):
                continue
            GJ = fold_graph(xg + [g])
            GH = intersect(GJ, GB)
            BH = basis(GH)
            r = len(BH[1])
            rels = [coords(GH, BH, w) for w in xg]
            rows = []
            for rel in rels:
                v = [0] * r
                for i, e in rel:
                    v[i] += e
                rows.append(v)
            hom = max(r - rank_mod_p(rows, p, r) for p in (2, 3))
            d = best_S3(r, rels)
            if d is None:
                skipped += 1
            lb = max(hom, d or 0)
            tested += 1
            hist[(r, lb)] = hist.get((r, lb), 0) + 1
            if lb > 1:
                viol += 1
                print('VIOLATION', name, 'g =', g, 'rk H =', r, 'hom', hom,
                      'S3', d, flush=True)
    print('j', j, gname, 'X count', len(Xs), 'tested', tested, 'S3-skipped',
          skipped, 'violations', viol)
    print('hist (rk H, lower bound):', sorted(hist.items()))


def selftest():
    """The hand example: B = <b, a b^2 a^-1>, X = ker(B -> S3), g = a."""
    GB = fold_graph(['b', 'abbA'])
    _, bg, _ = basis(GB)
    imgs = {'b': (1, 2, 0), 'abbA': (1, 0, 2)}
    ps = [imgs[w] for w in bg]
    GX = kernel_graph(GB, [regular(S3, p) for p in ps])
    _, xg, _ = basis(GX)
    GJ = fold_graph(xg + ['a'])
    GH = intersect(GJ, GB)
    BH = basis(GH)
    rels = [coords(GH, BH, w) for w in xg]
    print('selftest: B basis', bg, 'rk X', rank(GX), 'J = F:',
          len(GJ[0]) == 1, 'rk H', len(BH[1]),
          'S3 bound', best_S3(len(BH[1]), rels))


if __name__ == '__main__' and sys.argv[1] == 'selftest':
    selftest()
elif __name__ == '__main__':
    run(int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]),
        int(sys.argv[5]) if len(sys.argv) > 5 else 0)
