import itertools, sys, os, pickle
from tp import M, red, I, canon, census_rules
from census_moves import minimal
# Class I_0: one doubly blind coordinate pair (i, j), no two-site move. Three-site path over free memory:
# s0 read at address k by window 1, s1 read at i by window 1 and at j by window g2 = i j^-1, s2 read at k by g2.
KNOWN = {'A': 'breaker', 'B': 'breaker', 'Ab': 'breaker', 'AB': 'Z', 'AAB': 'Z', 'AAb': 'Z', 'ABB': 'Z', 'Abb': 'Z',
         'AAAb': 'Z', 'Abbb': 'Z', 'AAbAb': 'Z', 'AbAbb': 'Z', 'AAbb': 'Klein', 'ABAb': 'Klein', 'ABaB': 'Klein',
         'ABab': 'Z2', 'AA': 'a2', 'AAA': 'a3', 'BB': 'b2', 'BBB': 'b3', 'AbAb': 'c2', 'AbAbAb': 'c3',
         # lengths 5 and 6 by Magnus rewriting (census artifact Section 6): ascending HNN extensions of Z
         'AABAb': 'BS', 'AABab': 'BS', 'AAbaB': 'BS', 'ABBab': 'BS', 'ABaBB': 'BS', 'ABabb': 'BS', 'ABaBab': 'BS',
         'ABabAb': 'BS', 'AAbAbb': 'BS'}
# Not amenable, kept by canonical word: F_2 x| Z for ABAbb ABBAb ABAbAb ABaBAb AABaB AAbab ABaBaB; torus knot AAAbb AAbbb.
AMEN = {'breaker', 'Z', 'Klein', 'Z2', 'BS'}
def path(i, j, k):
    s0, s1 = M[k], M[i]
    g2 = red(M[i] + I(M[j]))
    s2 = red(g2 + M[k])
    S = [s0, s1, s2]
    wins = []
    for s in S:
        for n in M:
            g = red(s + I(n))
            if g not in wins:
                wins.append(g)
    winsites = [(g, [red(g + n) for n in M]) for g in wins]
    sites = []
    for g, st in winsites:
        for w in st:
            if w not in sites:
                sites.append(w)
    return S, winsites, sites
def path_sets(mu, i, j, k):
    S, winsites, sites = path(i, j, k)
    pairs = []
    for u, w in itertools.combinations(sites, 2):
        r = canon(I(u) + w)
        if KNOWN.get(r) in AMEN:
            continue
        pairs.append((u, w, r))
    out = set()
    changes = [(x, y) for x in range(3) for y in range(3) if x != y]
    for ch in itertools.product(changes, repeat=3):
        base0 = {s: c[0] for s, c in zip(S, ch)}; base1 = {s: c[1] for s, c in zip(S, ch)}
        options = []
        for g, st in winsites:
            cs = [w for w in st if w not in base0]
            opts = []
            for vals in itertools.product(range(3), repeat=len(cs)):
                x0 = dict(base0); x1 = dict(base1)
                for w, v in zip(cs, vals):
                    x0[w] = v; x1[w] = v
                if mu[tuple(x0[w] for w in st)] == mu[tuple(x1[w] for w in st)]:
                    opts.append(tuple(zip(cs, vals)))
            if not opts:
                break
            options.append(opts)
        else:
            for combo in itertools.product(*options):
                x = dict(base0)
                for part in combo:
                    x.update(part)
                conf = set()
                for u, w, r in pairs:
                    if u in base0 and w in base0:
                        if (base0[u], base1[u]) != (base0[w], base1[w]):
                            conf.add(r)
                    elif u in base0 or w in base0 or x[u] != x[w]:
                        conf.add(r)
                out.add(frozenset(conf))
    return minimal(out)
if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'universe':
        for i, j in [(0, 1), (0, 2), (1, 2)]:
            k = 3 - i - j
            S, winsites, sites = path(i, j, k)
            groups = {}
            for u, w in itertools.combinations(sites, 2):
                groups.setdefault(canon(I(u) + w), []).append('%s=%s' % (u or '1', w or '1'))
            print('double pair', M[i] or '1', M[j] or '1', 'support', [s or '1' for s in S], 'sites', len(sites))
            for r in sorted(groups, key=lambda w: (len(w), w)):
                print('   %-10s %-8s %s' % (r, KNOWN.get(r, '?'), ' '.join(groups[r])))
        sys.exit()
    stats = {}
    unknown = {}
    for key, mu, B in census_rules():
        double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
        if len(double) != 1:
            continue
        i, j = double[0]
        # I_0 rules only: no two-site shape (checked in census_moves); here require no shape-type absorption
        from census_moves import shape_sets
        from tp import SHAPES
        if any(shape_sets(mu, m, m2) for m, m2 in SHAPES):
            continue
        k = 3 - i - j
        sets = path_sets(mu, i, j, k)
        desc = tuple(sorted(','.join(sorted(KNOWN.get(r, r) for r in F)) for F in sets)) if sets else ('NO PATH MOVE',)
        for F in sets:
            for r in F:
                if r not in KNOWN:
                    unknown[r] = unknown.get(r, 0) + 1
        tag = ((M[i] or '1') + M[j], desc)
        stats.setdefault(tag, []).append(key)
    for tag in sorted(stats, key=str):
        print(len(stats[tag]), tag, 'eg', stats[tag][0], flush=True)
    print('unknown relators in minimal sets', sorted(unknown.items(), key=lambda t: (len(t[0]), t[0])))
