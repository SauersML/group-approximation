"""General (RI_B) hunt with nonabelian finite quotients.

For B = <Bgens> of rank r and a surjection rho : B -> G onto a finite group G
with d(G) = r (so rk(B : ker rho) = d(G) = r, since ker rho is normal),
search g with <ker rho, g> containing B.  A hit means
rk((J cap B) : X) = r > 1 = rk(J : X) for J = <X, g>, X = ker rho:
(RI_B) fails.  Usage: python3 searchB.py <mode> ...
"""
import itertools
import random
import sys
from stall import fold_graph, member, rank, basis, red, L, inv
from cover import kernel_graph


def compose(p, q):
    return tuple(p[i] for i in q)


def closure(gens):
    n = len(gens[0])
    seen = {tuple(range(n))}
    fr = list(seen)
    while fr:
        x = fr.pop()
        for y in gens:
            z = compose(y, x)
            if z not in seen:
                seen.add(z)
                fr.append(z)
    return sorted(seen)


def regular(elts, p):
    return tuple(elts.index(compose(p, x)) for x in elts)


def S(n):
    return list(itertools.permutations(range(n)))


def A(n):
    def sign(p):
        s, seen = 1, set()
        for i in range(n):
            if i in seen:
                continue
            j, c = i, 0
            while j not in seen:
                seen.add(j)
                j = p[j]
                c += 1
            s *= (-1) ** (c - 1)
        return s
    return [p for p in S(n) if sign(p) == 1]


GROUPS = {'S3': S(3), 'A4': A(4), 'S4': S(4), 'A5': A(5)}


def words(maxlen):
    frontier = ['']
    for _ in range(maxlen):
        new = [w + x for w in frontier for x in 'aAbB'
               if not w or red(w[-1] + x) != '']
        yield from new
        frontier = new


def surjections(gname, r, limit, rng):
    elts = GROUPS[gname]
    order = len(elts)
    out = []
    tries = 0
    while len(out) < limit and tries < 200 * limit:
        tries += 1
        ps = [rng.choice(elts) for _ in range(r)]
        if len(closure(ps)) == order:
            out.append(ps)
    return elts, out


def hunt(Bgens, gname, maxlen, nrho, seed=0, verbose=True):
    rng = random.Random(seed)
    GB = fold_graph(Bgens)
    r = rank(GB)
    elts, rhos = surjections(gname, r, nrho, rng)
    hits = []
    for ps in rhos:
        GX = kernel_graph(GB, [regular(elts, p) for p in ps])
        _, xg, _ = basis(GX)
        assert rank(GX) == 1 + len(elts) * (r - 1)
        for g in words(maxlen):
            if member(GB, g):
                continue
            GJ = fold_graph(xg + [g])
            if all(member(GJ, w) for w in Bgens):
                hits.append((ps, g, rank(GJ)))
                if verbose:
                    print('  HIT', gname, ps, 'g =', g, 'rk J =', rank(GJ))
                break
    return r, len(rhos), hits


def rand_word(rng, n):
    w = ''
    while len(w) < n:
        w = red(w + rng.choice('aAbB'))
    return w


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'chain':
        for j in (1, 2):
            for gname in ('S3', 'A4', 'A5'):
                r, n, h = hunt(L(j), gname, int(sys.argv[2]), 12)
                print('L_%d' % j, gname, 'rhos', n, 'hits', len(h), flush=True)
    elif mode == 'rank3':
        B = ['aBAB', 'bbAA', 'AbaBa']
        for gname in ('S3', 'A4'):
            r, n, h = hunt(B, gname, int(sys.argv[2]), 12)
            print('rank3', gname, 'rhos', n, 'hits', len(h), flush=True)
    elif mode in ('random', 'malrandom', 'nonmal'):
        from maln import malnormal
        rk, ntr, lw, ml = map(int, sys.argv[2:6])
        gname = sys.argv[6] if len(sys.argv) > 6 else 'S3'
        rng = random.Random(1)
        tot = hitsB = 0
        for t in range(ntr):
            B = [rand_word(rng, rng.randint(1, lw)) for _ in range(rk)]
            GB = fold_graph(B)
            if rank(GB) != rk:
                continue
            if mode == 'malrandom' and not malnormal(GB):
                continue
            if mode == 'nonmal' and malnormal(GB):
                continue
            tot += 1
            r, n, h = hunt(B, gname, ml, 4, seed=t, verbose=False)
            if h:
                hitsB += 1
                print('B', B, 'HIT', h[0], flush=True)
        print(mode, gname, 'rank', rk, 'subgroups', tot, 'with hits', hitsB)
