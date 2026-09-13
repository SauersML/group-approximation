import itertools
# Shared helpers for the rigid two-patch census: rules, blind pairs, free-group words, canonical relators.
Y = list(itertools.product(range(3), repeat=3))
PAIRS = [(0, 1), (0, 2), (1, 2)]
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
M = ['', 'a', 'b']
def red(w):
    out = []
    for ch in w:
        if out and out[-1] == INV[ch]:
            out.pop()
        else:
            out.append(ch)
    return ''.join(out)
def I(w):
    return ''.join(INV[ch] for ch in reversed(w))
def canon(r):
    # cyclic word up to rotation and inversion
    r = red(r)
    while len(r) >= 2 and r[-1] == INV[r[0]]:
        r = r[1:-1]
    cands = []
    for w in (r, I(r)):
        for k in range(max(1, len(w))):
            cands.append(w[k:] + w[:k])
    return min(cands, key=lambda w: (len(w), w))
def rule(c, p, q, tp, tq):
    tab = {}
    for y in Y:
        v = (c[0] * y[0] + c[1] * y[1] + c[2] * y[2]) % 3
        if y == p: v = (v + tp) % 3
        if y == q: v = (v + tq) % 3
        tab[y] = v
    return tab
def put(ctx, i, u):
    y = list(ctx); y.insert(i, u); return tuple(y)
def blind(mu, i):
    out = set()
    for u, v in PAIRS:
        for ctx in itertools.product(range(3), repeat=2):
            if mu[put(ctx, i, u)] == mu[put(ctx, i, v)]:
                out.add((u, v)); break
    return out
def census_rules():
    # rigid, unbalanced, injective diagonal; yields (key, mu, B)
    for c in [(1, 1, 2), (1, 1, 0)]:
        for p, q in itertools.combinations(Y, 2):
            if not set(p) & set(q):
                continue
            for tp, tq in itertools.product((1, 2), repeat=2):
                mu = rule(c, p, q, tp, tq)
                counts = [sum(1 for y in Y if mu[y] == k) for k in range(3)]
                if counts == [9, 9, 9]:
                    continue
                B = [blind(mu, i) for i in range(3)]
                if B[0] & B[1] & B[2]:
                    continue
                if len({mu[(v, v, v)] for v in range(3)}) < 3:
                    continue
                yield (c, p, q, tp, tq), mu, B
# two-site shapes: shared window 1 reads s at address index m and t at index m2
SHAPES = [(0, 1), (0, 2), (1, 2)]
def shape_words(m, m2):
    s, t = M[m], M[m2]
    wins = sorted({red(x + I(n)) for x in (s, t) for n in M}, key=lambda w: (len(w), w))
    sites = []
    for g in wins:
        for n in M:
            w = red(g + n)
            if w not in sites:
                sites.append(w)
    return s, t, wins, sites
if __name__ == '__main__':
    for m, m2 in SHAPES:
        s, t, wins, sites = shape_words(m, m2)
        print('shape s=%s t=%s windows %s sites(%d) %s' % (s or '1', t or '1', [g or '1' for g in wins], len(sites), [w or '1' for w in sites]))
        groups = {}
        for u, w in itertools.combinations(sites, 2):
            groups.setdefault(canon(I(u) + w), []).append((u or '1', w or '1'))
        for r in sorted(groups, key=lambda w: (len(w), w)):
            print('   %-8s %s' % (r, ' '.join('%s=%s' % pw for pw in groups[r])))
