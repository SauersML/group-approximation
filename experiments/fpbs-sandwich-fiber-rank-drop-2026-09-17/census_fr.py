"""Rank-drop test in F_r for r >= 2 (letters a,b,c,...; inverses upper case).

For K <= F_r, N of index d with K N = F_r, H = K cap N:
  rmin(K)  = least rank of an overgroup of K in F_r (quotients of Gamma(K)),
  mrk_N(H) = least rank of M' with H <= M' <= N (colour-respecting quotients
             of Gamma(H)),
  forced   = 1 + d (rmin(K) - 1)  (attained by M cap N, M least-rank overgroup).
Hanna Neumann (Friedman) gives mrk_N(H) >= 1 + d whenever rk K >= 2, so a
drop mrk < forced is impossible when rmin(K) = 2 (e.g. every K in F_2).
This script looks for drops when rmin(K) >= 3 (needs r >= 3).

Usage: python3 census_fr.py r seed trials ngen maxlen dmin dmax vmax limit
"""
import itertools, random, sys, collections
from census import set_partitions


def inv(c):
    return c.upper() if c.islower() else c.lower()


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == inv(c):
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def fold(nv, edges):
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    E = list(edges)
    changed = True
    while changed:
        changed = False
        out, inn = {}, {}
        for (u, l, v) in E:
            u, v = find(u), find(v)
            if (u, l) in out and find(out[(u, l)]) != v:
                parent[find(out[(u, l)])] = v
                changed = True
                break
            out[(u, l)] = v
            if (v, l) in inn and find(inn[(v, l)]) != u:
                parent[find(inn[(v, l)])] = u
                changed = True
                break
            inn[(v, l)] = u
    roots = sorted({find(x) for x in range(nv)})
    idx = {r0: i for i, r0 in enumerate(roots)}
    return len(roots), sorted({(idx[find(u)], l, idx[find(v)]) for (u, l, v) in E})


def stallings(gens):
    nv, edges = 1, []
    for w in gens:
        w = reduce(w)
        cur = 0
        for i, c in enumerate(w):
            nxt = 0 if i == len(w) - 1 else nv
            if nxt != 0:
                nv += 1
            if c.islower():
                edges.append((cur, c, nxt))
            else:
                edges.append((nxt, c.lower(), cur))
            cur = nxt
    return fold(nv, edges)


def rank(nv, E):
    return len(E) - nv + 1


def min_quotient_rank(nv, E, classes, limit):
    best = rank(nv, E)
    count = 0
    for combo in itertools.product(*[list(set_partitions(c)) for c in classes]):
        count += 1
        if count > limit:
            return best, False
        parent = list(range(nv))

        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for part in combo:
            for blk in part:
                for x in blk[1:]:
                    parent[find(x)] = find(blk[0])
        reps = sorted({find(x) for x in range(nv)})
        ri = {r0: i for i, r0 in enumerate(reps)}
        m, F = fold(len(reps), [(ri[find(u)], l, ri[find(v)]) for (u, l, v) in E])
        best = min(best, rank(m, F))
    return best, True


def product(K, P, d):
    nv, E = K
    out, inn = {}, {}
    for (u, l, v) in E:
        out.setdefault(u, []).append((l, v))
        inn.setdefault(v, []).append((l, u))
    seen = {(0, 0): 0}
    order = [(0, 0)]
    i = 0
    while i < len(order):
        (u, c) = order[i]
        i += 1
        for (l, v) in out.get(u, []):
            t = (v, P[l][c])
            if t not in seen:
                seen[t] = len(order); order.append(t)
        for (l, w) in inn.get(u, []):
            t = (w, P[l].index(c))
            if t not in seen:
                seen[t] = len(order); order.append(t)
    PE = sorted({(seen[(u, c)], l, seen[(v, P[l][c])]) for (u, l, v) in E
                 for c in range(d) if (u, c) in seen})
    trans = all((0, c) in seen for c in range(d))
    return len(order), PE, [c for (_, c) in order], trans


def main(r, seed, trials, ngen, maxlen, dmin, dmax, vmax, limit):
    letters = 'abcdefgh'[:r]
    alph = letters + letters.upper()
    rng = random.Random(seed)
    stats = collections.Counter()
    done = drops = 0
    while done < trials:
        gens = []
        for _ in range(ngen):
            L = rng.randint(1, maxlen)
            w = ''
            while len(w) < L:
                c = rng.choice(alph)
                if not (w and inv(c) == w[-1]):
                    w += c
            gens.append(w)
        nv, E = stallings(gens)
        if rank(nv, E) != ngen or nv > vmax:
            continue
        rmin, ok = min_quotient_rank(nv, E, [list(range(nv))], limit)
        if rmin < 3:
            continue  # drops impossible by Hanna Neumann
        d = rng.randint(dmin, dmax)
        P = {}
        for l in letters:
            p = list(range(d)); rng.shuffle(p); P[l] = tuple(p)
        n, PE, col, trans = product((nv, E), P, d)
        if not trans:
            continue
        done += 1
        classes = [[i for i in range(n) if col[i] == c] for c in range(d)]
        mrk, complete = min_quotient_rank(n, PE, classes, limit)
        forced = 1 + d * (rmin - 1)
        stats[(ngen, rmin, d, mrk - forced, mrk - (1 + d), complete)] += 1
        if mrk < forced:
            drops += 1
            print('DROP', gens, P, 'rmin', rmin, 'mrk', mrk, 'forced', forced,
                  complete, flush=True)
    print('trials', done, 'drops', drops)
    print('key: (rk K, rmin K, d, mrk - forced, mrk - (1+d), complete)')
    for k in sorted(stats, key=str):
        print(k, stats[k])


if __name__ == '__main__':
    main(*[int(x) for x in sys.argv[1:]])
