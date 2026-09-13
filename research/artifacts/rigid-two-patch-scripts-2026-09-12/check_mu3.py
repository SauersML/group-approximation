import itertools
# mu_3 = y1 + ya - yb + [y=(0,0,2)] + [y=(1,2,0)] over F_3
def mu(y):
    v = (y[0] + y[1] - y[2]) % 3
    if y == (0, 0, 2) or y == (1, 2, 0):
        v = (v + 1) % 3
    return v
inv = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
def red(w):
    out = []
    for c in w:
        if out and out[-1] == inv[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)
def I(w):
    return ''.join(inv[c] for c in reversed(w))
M = ['', 'a', 'b']
G1 = {'A': 1, 'Ab': 0, 'B': 1, 'Ba': 2}
Ga = {'aa': 2, 'ab': 0, 'aB': 0, 'aBa': 0}
Gb = {'ba': 0, 'bb': 2, 'bA': 0, 'bAb': 2}
moves = {
    'T_ab': ({'a': (1, 2), 'b': (0, 1)}, [Ga, Gb], ''),
    'T_1a': ({'': (0, 2), 'a': (1, 2)}, [G1, Ga], 'b'),
    'T_1b': ({'': (0, 2), 'b': (1, 0)}, [G1, Gb], 'a'),
    'T_1ab': ({'': (0, 2), 'a': (2, 1), 'b': (0, 1)}, [G1, Ga, Gb], None),
}
for name, (ch, gads, free) in moves.items():
    ctx = {}
    for g in gads:
        ctx.update(g)
    ok = True
    for fv in range(3):
        x = dict(ctx); xp = dict(ctx)
        for s, (u, v) in ch.items():
            x[s] = u; xp[s] = v
        if free is not None:
            x[free] = fv; xp[free] = fv
        wins = set(red(s + I(m)) for s in ch for m in M)
        for g in wins:
            sites = [red(g + m) for m in M]
            if any(s not in x for s in sites):
                print(name, 'UNDEFINED site in window', g, sites); ok = False; continue
            y = tuple(x[s] for s in sites); yp = tuple(xp[s] for s in sites)
            if mu(y) != mu(yp):
                print(name, 'free', fv, 'window', g or '1', y, yp, mu(y), mu(yp)); ok = False
        if free is None:
            break
    print(name, 'generic collision OK' if ok else 'FAILS')
    words = sorted(set(list(ctx) + list(ch) + ([free] if free is not None else [])), key=len)
    for u, w in itertools.combinations(words, 2):
        r = red(I(u) + w)
        vu = 'chg' if u in ch else ('free' if u == free else ctx[u])
        vw = 'chg' if w in ch else ('free' if w == free else ctx[w])
        tag = 'agree' if (vu == vw and vu not in ('chg',)) or 'free' in (vu, vw) else 'CONFLICT'
        print('  ', name, (u or '1'), '=', (w or '1'), 'relator', r or '1', vu, vw, tag)
counts = [0, 0, 0]
for y in itertools.product(range(3), repeat=3):
    counts[mu(y)] += 1
print('counts', counts)
