import itertools, sys
# mu_3 = y1 + ya - yb + [y=(0,0,2)] + [y=(1,2,0)] over F_3, placement (1, a, b)
def mu(y):
    v = (y[0] + y[1] - y[2]) % 3
    if y == (0, 0, 2) or y == (1, 2, 0):
        v = (v + 1) % 3
    return v
# group model: stack rewriting with 2-letter cancellation rules (free product normal forms)
MODELS = {
    'F2': ({'aA', 'Aa', 'bB', 'Bb'}, {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}, ['', 'a', 'b']),
    'Z*Z2': ({'aA', 'Aa', 'cc'}, {'a': 'A', 'A': 'a', 'c': 'c'}, ['', 'a', 'ac']),
}
def run(model, S, maxsol):
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
    S = [red(s) for s in S]
    W = sorted(set(red(s + I(m)) for s in S for m in M), key=lambda w: (len(w), w))
    wins = [(g, [red(g + m) for m in M]) for g in W]
    sites = []
    for g, st in wins:
        for t in st:
            if t not in sites:
                sites.append(t)
    ctx = [t for t in sites if t not in S]
    pos = {t: i for i, t in enumerate(ctx)}
    check_at = {i: [] for i in range(-1, len(ctx))}
    for g, st in wins:
        check_at[max([pos[t] for t in st if t in pos], default=-1)].append(st)
    ok = lambda st, x0, x1: mu(tuple(x0[t] for t in st)) == mu(tuple(x1[t] for t in st))
    sols = []
    for ch in itertools.product([(u, v) for u in range(3) for v in range(3) if u != v], repeat=len(S)):
        x0 = {s: ch[i][0] for i, s in enumerate(S)}
        x1 = {s: ch[i][1] for i, s in enumerate(S)}
        if not all(ok(st, x0, x1) for st in check_at[-1]):
            continue
        def bt(i):
            if len(sols) >= maxsol:
                return
            if i == len(ctx):
                sols.append((dict(x0), dict(x1)))
                return
            t = ctx[i]
            for v in range(3):
                x0[t] = v; x1[t] = v
                if all(ok(st, x0, x1) for st in check_at[i]):
                    bt(i + 1)
            del x0[t]; del x1[t]
        bt(0)
    print('model', model, 'S', [s or '1' for s in S], 'windows', [g or '1' for g in W], 'solutions', len(sols))
    for x0, x1 in sols[:3]:
        print('   ', ' '.join((t or '1') + ('=%d>%d' % (x0[t], x1[t]) if t in S else '=%d' % x0[t]) for t in sites))
    return sols
if __name__ == '__main__':
    model = sys.argv[1]
    S = sys.argv[2].split(',')
    S = ['' if s == '1' else s for s in S]
    run(model, S, int(sys.argv[3]) if len(sys.argv) > 3 else 100000)
