import itertools, sys
# Generalized collisions (with don't-care sites) for mu_3 in a free-product model, and their conflict relators.
def mu(y):
    v = (y[0] + y[1] - y[2]) % 3
    if y == (0, 0, 2) or y == (1, 2, 0):
        v = (v + 1) % 3
    return v
MODELS = {
    'F2': ({'aA', 'Aa', 'bB', 'Bb'}, {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}, ['', 'a', 'b']),
    'Z*Z2': ({'aA', 'Aa', 'cc'}, {'a': 'A', 'A': 'a', 'c': 'c'}, ['', 'a', 'ac']),
}
model, S = sys.argv[1], ['' if s == '1' else s for s in sys.argv[2].split(',')]
pairs, inv, M = MODELS[model]
def red(w):
    out = []
    for ch in w:
        if out and (out[-1] + ch) in pairs:
            out.pop()
        else:
            out.append(ch)
    return ''.join(out)
I = lambda w: ''.join(inv[ch] for ch in reversed(w))
def canon(r):
    r = red(r)
    while len(r) >= 2 and (r[-1] + r[0]) in pairs:
        r = red(r[1:-1])
    if len(r) == 1 and r + r in pairs:
        pass
    cands = []
    for w in (r, I(r)):
        for k in range(max(1, len(w))):
            cands.append(w[k:] + w[:k])
    return min(cands, key=lambda w: (len(w), w))
S = [red(s) for s in S]
W = sorted(set(red(s + I(m)) for s in S for m in M), key=lambda w: (len(w), w))
wins = [[red(g + m) for m in M] for g in W]
sites = []
for st in wins:
    for t in st:
        if t not in sites:
            sites.append(t)
ctx = [t for t in sites if t not in S]
def valid(x0, x1):
    return all(mu(tuple(x0[t] for t in st)) == mu(tuple(x1[t] for t in st)) for st in wins)
best = None
for ch in itertools.product([(u, v) for u in range(3) for v in range(3) if u != v], repeat=len(S)):
    for vals in itertools.product(range(3), repeat=len(ctx)):
        x0 = {s: ch[i][0] for i, s in enumerate(S)}
        x1 = {s: ch[i][1] for i, s in enumerate(S)}
        for t, v in zip(ctx, vals):
            x0[t] = v; x1[t] = v
        if not valid(x0, x1):
            continue
        free = []
        for t in ctx:
            if all(valid({**x0, t: v}, {**x1, t: v}) for v in range(3)):
                free.append(t)
        # the whole free cube must be valid
        cube_ok = all(valid({**x0, **dict(zip(free, vv))}, {**x1, **dict(zip(free, vv))})
                      for vv in itertools.product(range(3), repeat=len(free)))
        if not cube_ok:
            continue
        rels = set()
        for u, w in itertools.combinations(sites, 2):
            if u in free or w in free:
                if u in S or w in S:
                    rels.add(canon(I(u) + w))
                continue
            if u in S and w in S:
                if (x0[u], x1[u]) != (x0[w], x1[w]):
                    rels.add(canon(I(u) + w))
            elif u in S or w in S:
                rels.add(canon(I(u) + w))
            elif x0[u] != x0[w]:
                rels.add(canon(I(u) + w))
        key = (len(rels), -len(free))
        if best is None or key < best[0]:
            best = (key, dict(x0), dict(x1), free, sorted(rels, key=lambda w: (len(w), w)))
key, x0, x1, free, rels = best
print('model', model, 'S', [s or '1' for s in S], 'windows', [g or '1' for g in W])
print('  sites', ' '.join((t or '1') + ('=%d>%d' % (x0[t], x1[t]) if t in S else ('=*' if t in free else '=%d' % x0[t])) for t in sites))
print('  conflict relators (canonical, up to rotation and inverse):', len(rels))
print('  ', ' '.join(rels))
