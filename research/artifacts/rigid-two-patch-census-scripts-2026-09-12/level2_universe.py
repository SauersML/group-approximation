import itertools
from tp import M
from level2 import model, mul, inv, canon
# All coincidence relators of the d-cycle support {1, d, ..., d^(k-1)} in the model Z/k * Z, for hand classification.
def show(u, orders, names):
    out = []
    for g, e in u:
        if orders[g] and e > orders[g] // 2:
            e -= orders[g]
        nm = names[g]
        out.append(nm + ('^%d' % e if e != 1 else ''))
    return ' '.join(out) or '1'
def geometry(r):
    orders, img, _ = model(r)
    d, k = r[0], int(r[1])
    names = {'T': d, 'X': 'b' if d == 'a' else 'a'}
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
    sites = []
    for g in wins:
        for n in M:
            w = mul(g, img[n], orders)
            if w not in sites:
                sites.append(w)
    return orders, names, S, wins, sites
if __name__ == '__main__':
    for r in ['a2', 'b2', 'c2', 'a3', 'b3', 'c3']:
        orders, names, S, wins, sites = geometry(r)
        sh = lambda u: show(u, orders, names)
        print('model', r, 'support', [sh(s) for s in S], 'windows', [sh(g) for g in wins], 'sites', len(sites))
        groups = {}
        for u, w in itertools.combinations(sites, 2):
            groups.setdefault(canon(mul(inv(u, orders), w, orders), orders), []).append('%s=%s' % (sh(u), sh(w)))
        for rel in sorted(groups, key=lambda w: (len(w), w)):
            print('   %-22s %s' % (sh(rel), '  '.join(groups[rel])))
