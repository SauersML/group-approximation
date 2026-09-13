import itertools, sys
from tp import M, census_rules, SHAPES
from census_moves import shape_sets, residuals, minimal
# Level 2: in the model group Z/k * Z where the residual relator d^k holds, the d-cycle support {1, d, ..., d^(k-1)}.
# Model elements: tuples of syllables (gen, exp); gen 'T' has order k, gen 'X' is free (order 0).
def norm(g, e, orders):
    return e % orders[g] if orders[g] else e
def mul(u, v, orders):
    out = list(u)
    for g, e in v:
        if out and out[-1][0] == g:
            e2 = norm(g, out[-1][1] + e, orders)
            out.pop()
            if e2:
                out.append((g, e2))
        else:
            out.append((g, norm(g, e, orders)))
    return tuple(out)
def inv(u, orders):
    return tuple((g, norm(g, -e, orders)) for g, e in reversed(u))
def canon(u, orders):
    u = list(u)
    while len(u) >= 2 and u[0][0] == u[-1][0]:
        e2 = norm(u[0][0], u[0][1] + u[-1][1], orders)
        g = u[0][0]
        u = u[1:-1]
        if e2:
            u = [(g, e2)] + u if not u or u[0][0] != g else None
            if u is None:
                return canon_fallback
    cands = []
    for w in (u, list(inv(tuple(u), orders))):
        for k in range(max(1, len(w))):
            cands.append(tuple(w[k:] + w[:k]))
    return min(cands, key=lambda w: (len(w), w))
canon_fallback = None
def show(u, orders):
    return ''.join('%s%s' % (g.lower() if e > 0 else g, abs(e) if abs(e) > 1 else '') for g, e in
                   ((g, (e if orders[g] == 0 or e <= orders[g] // 2 else e - orders[g])) for g, e in u)) or '1'
# residual relator -> model: images of a, b and orders
def model(r):
    d, k = r[0], int(r[1])
    orders = {'T': k, 'X': 0}
    T, X = (('T', 1),), (('X', 1),)
    if d == 'a':
        A, B = T, X
    elif d == 'b':
        A, B = X, T
    else:  # c = a^-1 b of order k, basis (a, c): b = a c
        A, B = X, X + T
    return orders, {'': (), 'a': A, 'b': B}, {'a': 'T', 'b': 'X'} if d == 'a' else ({'a': 'X', 'b': 'T'} if d == 'b' else {'a': 'X', 'c': 'T'})
def cycle_sets(mu, r):
    orders, img, names = model(r)
    d, k = r[0], int(r[1])
    Minv = [inv(img[n], orders) for n in M]
    delta = img['a'] if d == 'a' else (img['b'] if d == 'b' else (('T', 1),))
    S = [()]
    for _ in range(k - 1):
        S.append(mul(S[-1], delta, orders))
    wins = []
    for s in S:
        for mi in Minv:
            g = mul(s, mi, orders)
            if g not in wins:
                wins.append(g)
    winsites = {g: [mul(g, img[n], orders) for n in M] for g in wins}
    sites = []
    for g in wins:
        for w in winsites[g]:
            if w not in sites:
                sites.append(w)
    pairs = []
    for u, w in itertools.combinations(sites, 2):
        pairs.append((u, w, canon(mul(inv(u, orders), w, orders), orders)))
    out = set()
    changes = [(x, y) for x in range(3) for y in range(3) if x != y]
    for ch in itertools.product(changes, repeat=len(S)):
        base0 = {s: c[0] for s, c in zip(S, ch)}; base1 = {s: c[1] for s, c in zip(S, ch)}
        options = []
        for g, st in winsites.items():
            cs = []
            for w in st:
                if w not in base0 and w not in cs:
                    cs.append(w)
            opts = []
            for vals in itertools.product(range(3), repeat=len(cs)):
                x0 = dict(base0); x1 = dict(base1)
                for w, val in zip(cs, vals):
                    x0[w] = val; x1[w] = val
                if mu[tuple(x0[w] for w in st)] == mu[tuple(x1[w] for w in st)]:
                    opts.append(dict(zip(cs, vals)))
            if not opts:
                break
            options.append(opts)
        else:
            for combo in itertools.product(*options):
                x = {}
                ok = True
                for part in combo:
                    for w, val in part.items():
                        if x.setdefault(w, val) != val:
                            ok = False
                if not ok:
                    continue
                conf = set()
                for u, w, rel in pairs:
                    if u in base0 and w in base0:
                        if (base0[u], base1[u]) != (base0[w], base1[w]):
                            conf.add(rel)
                    elif u in base0 or w in base0 or x[u] != x[w]:
                        conf.add(rel)
                out.add(frozenset(conf))
    return minimal(out), orders, sites
if __name__ == '__main__':
    stats = {}
    for key, mu, B in census_rules():
        per = {}
        for m, m2 in SHAPES:
            sets = shape_sets(mu, m, m2)
            if sets:
                per[(m, m2)] = sets
        if not per:
            continue
        res = residuals([F for sets in per.values() for F in sets])
        needed = sorted({r for R in res for r in R})
        for r in needed:
            sets, orders, sites = cycle_sets(mu, r)
            desc = tuple(sorted(','.join(sorted(show(w, orders) for w in F)) for F in sets)) if sets else ('NO MOVE',)
            tag = (key[0], r, desc)
            stats.setdefault(tag, []).append(key)
    for tag in sorted(stats, key=str):
        print(len(stats[tag]), tag, 'eg', stats[tag][0])
