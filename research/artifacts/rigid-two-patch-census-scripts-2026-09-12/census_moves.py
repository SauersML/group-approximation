import itertools, sys
from tp import M, red, I, canon, census_rules, shape_words, SHAPES
# Level 1: for each rule, each two-site shape, the minimal sets of nonamenable conflict relators over all valid moves.
# Nonamenable relators among all 55 pairs of every shape (hand classification in the census artifact):
TORS = {'AA': 'a2', 'AAA': 'a3', 'BB': 'b2', 'BBB': 'b3', 'AbAb': 'c2', 'AbAbAb': 'c3'}
GEN = {'a2': ('a', 2), 'a3': ('a', 3), 'b2': ('b', 2), 'b3': ('b', 3), 'c2': ('c', 2), 'c3': ('c', 3)}
def amenable(R):
    orders = {}
    for r in R:
        g, k = GEN[r]
        if g in orders and orders[g] != k:
            return True  # g^2 = g^3 = 1 breaks distinctness
        orders[g] = k
    if len(orders) == 3:
        return True
    return len(orders) == 2 and all(k == 2 for k in orders.values())
def minimal(sets):
    sets = set(sets)
    return sorted((S for S in sets if not any(T < S for T in sets)), key=lambda S: (len(S), sorted(S)))
PREP = {}
for m, m2 in SHAPES:
    s, t, wins, sites = shape_words(m, m2)
    rel = {}
    for u, w in itertools.combinations(sites, 2):
        r = canon(I(u) + w)
        if r in TORS:
            rel[(u, w)] = TORS[r]
    PREP[(m, m2)] = (s, t, wins, sites, rel)
def shape_sets(mu, m, m2):
    s, t, wins, sites, rel = PREP[(m, m2)]
    changed = {s, t}
    winsites = {g: [red(g + n) for n in M] for g in wins}
    ctx_sites = [w for w in sites if w not in changed]
    out = set()
    for (u, u2), (v, v2) in itertools.product([(x, y) for x in range(3) for y in range(3) if x != y], repeat=2):
        base0 = {s: u, t: v}; base1 = {s: u2, t: v2}
        # per window, the valid assignments of its context sites
        options = []
        for g, st in winsites.items():
            cs = [w for w in st if w not in changed]
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
                conf = frozenset(r for (p, w), r in rel.items() if p in changed or w in changed or x[p] != x[w])
                out.add(conf)
    return minimal(out)
def residuals(family):
    pats = []
    for choice in itertools.product([None, 2, 3], repeat=3):
        R = frozenset('%s%d' % (g, k) for g, k in zip('abc', choice) if k)
        if amenable(R):
            continue
        if all(R & F for F in family):
            pats.append(R)
    return minimal(pats)
if __name__ == '__main__':
    stats = {}
    examples = {}
    rows = []
    for key, mu, B in census_rules():
        per = {}
        for m, m2 in SHAPES:
            sets = shape_sets(mu, m, m2)
            if sets:
                per[(m, m2)] = sets
        double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
        if not double:
            continue  # class II
        cls = 'I%d' % len(per) if per else 'I0'
        fam = [F for sets in per.values() for F in sets]
        res = residuals(fam) if per else ['no two-site move']
        tag = (key[0], cls, tuple(sorted('%s%s' % (M[m] or '1', M[m2]) for m, m2 in per)),
               tuple(','.join(sorted(R)) if not isinstance(R, str) else R for R in res))
        stats[tag] = stats.get(tag, 0) + 1
        examples.setdefault(tag, (key, {('%s%s' % (M[m] or '1', M[m2])): [sorted(F) for F in sets] for (m, m2), sets in per.items()}))
        rows.append((key, tag))
    for tag in sorted(stats, key=str):
        print(stats[tag], tag, 'example', examples[tag])
    tot = {}
    for key, tag in rows:
        tot[(tag[0], tag[1])] = tot.get((tag[0], tag[1]), 0) + 1
    print('class totals', sorted(tot.items()))
