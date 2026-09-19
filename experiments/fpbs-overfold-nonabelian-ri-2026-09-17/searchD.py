"""Is the rank-2 failure of (RI_B) bounded?  B = <b, a b^2 a^-1> (not
malnormal), X = <random words in b, c = a b^2 a^-1>, J = <X, a>,
H = J cap B.  Lower bound for rk(H : X) = max(F_p cokernel dims (p=2,3,5),
S3 bound).  Reports the largest lower bound seen (rk(J : X) <= 1)."""
import random
import sys
from stall import fold_graph, member, rank, basis, coords, intersect, red, inv
from searchC import best_S3, rank_mod_p


def bword(rng, n):
    gens = {'b': 'b', 'B': 'B', 'c': 'abbA', 'C': 'aBBA'}
    w = ''
    while len(red(w)) < n:
        w = red(w + gens[rng.choice('bBcC')])
    return w


def main(trials, nx, lw, g='a', seed=0):
    rng = random.Random(seed)
    GB = fold_graph(['b', 'abbA'])
    best = {}
    for t in range(trials):
        xg = [bword(rng, rng.randint(2, lw)) for _ in range(nx)]
        GX = fold_graph(xg)
        if member(GX, g):
            continue
        GJ = fold_graph(xg + [g])
        GH = intersect(GJ, GB)
        BH = basis(GH)
        r = len(BH[1])
        _, xb, _ = basis(GX)
        rels = [coords(GH, BH, w) for w in xb]
        rows = []
        for rel in rels:
            v = [0] * r
            for i, e in rel:
                v[i] += e
            rows.append(v)
        hom = max(r - rank_mod_p(rows, p, r) for p in (2, 3, 5))
        d = best_S3(r, rels) if r <= 9 else 0
        lb = max(hom, d)
        if lb >= 2 and lb not in best:
            best[lb] = (xg, r, hom, d)
            print('lb', lb, 'X gens', xg, 'rk X', rank(GX), 'rk H', r,
                  'hom', hom, 'S3', d, flush=True)
    print('max lower bound on rk(J cap B : X) with rk(J : X) = 1:',
          max(best) if best else '<2')


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
