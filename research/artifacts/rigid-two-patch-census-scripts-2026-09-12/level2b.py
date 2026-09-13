import itertools, sys, os, pickle
from tp import M, census_rules, SHAPES
from census_moves import shape_sets, residuals, amenable
from level2 import model, mul, inv, canon
# Level 2 closure: residual d^2 -> d-swap support {1, d}; residual d^3 -> d-cycle support {1, d, d^-1}.
# Hand classification (artifact): every relator of a d-swap support is a breaker or amenable modulo d^2;
# the nonamenable relators of a d-cycle support modulo d^3 are exactly e^2 for the two generators e != d.
def geometry(r):
    orders, img, _ = model(r)
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
    winsites = [(g, [mul(g, img[n], orders) for n in M]) for g in wins]
    sites = []
    for g, st in winsites:
        for w in st:
            if w not in sites:
                sites.append(w)
    def word(wd):
        u = ()
        for ch in wd:
            u = mul(u, img[ch.lower()] if ch.islower() else inv(img[ch.lower()], orders), orders)
        return u
    labels = {canon(word(wd), orders): lab for wd, lab in (('AA', 'a2'), ('BB', 'b2'), ('AbAb', 'c2')) if lab[0] != d}
    tors = []
    for u, w in itertools.combinations(sites, 2):
        lab = labels.get(canon(mul(inv(u, orders), w, orders), orders))
        if lab:
            assert u not in S and w not in S, (r, u, w)
            tors.append((u, w, lab))
    return S, winsites, tors
GEOM = {r: geometry(r) for r in ['a2', 'b2', 'c2', 'a3', 'b3', 'c3']}
# --strict-swap reproduces level2b_strict_swap.txt: swaps with every e^2 context pair forced equal
RELAX = '--strict-swap' not in sys.argv
def feasible(mu, r, allowed):
    # a valid move on the support whose torsion conflicts all lie in `allowed`
    S, winsites, tors = GEOM[r]
    equal = [(u, w) for u, w, lab in tors if lab not in allowed]
    changes = [(x, y) for x in range(3) for y in range(3) if x != y]
    for ch in itertools.product(changes, repeat=len(S)):
        x0 = {s: c[0] for s, c in zip(S, ch)}; x1 = {s: c[1] for s, c in zip(S, ch)}
        def bt(i):
            if i == len(winsites):
                return True
            g, st = winsites[i]
            free = []
            for w in st:
                if w not in x0 and w not in free:
                    free.append(w)
            for vals in itertools.product(range(3), repeat=len(free)):
                for w, v in zip(free, vals):
                    x0[w] = v; x1[w] = v
                if (mu[tuple(x0[w] for w in st)] == mu[tuple(x1[w] for w in st)]
                        and all(x0[u] == x0[w] for u, w in equal if u in x0 and w in x0) and bt(i + 1)):
                    return True
                for w in free:
                    del x0[w]; del x1[w]
            return False
        if bt(0):
            return True
    return False
PATTERNS = []
for choice in itertools.product([None, 2, 3], repeat=3):
    P = frozenset('%s%d' % (g, k) for g, k in zip('abc', choice) if k)
    if not amenable(P):
        PATTERNS.append(P)
def close(mu, R, memo):
    def feas(r, allowed):
        key = (r, frozenset(allowed))
        if key not in memo:
            memo[key] = feasible(mu, r, allowed)
        return memo[key]
    used = set()
    for P in PATTERNS:
        if not R <= P:
            continue
        move = None
        for r in sorted(P):
            # Lemma 3.1: beside d^2 no e^2 holds in a nonamenable group (D_infinity), so no equalities are imposed
            if r[1] == '2' and feas(r, {'%s2' % e for e in 'abc' if e != r[0]} if RELAX else set()):
                move = '%s-swap' % r[0]; break
        if move is None:
            for r in sorted(P):
                if r[1] == '3':
                    others = {'%s2' % e for e in 'abc' if e != r[0]}
                    if feas(r, others - P):
                        move = '%s-cycle' % r[0]; break
        if move is None:
            return None, P
        used.add(move)
    return sorted(used), None
if __name__ == '__main__':
    cache = 'level1_rows.pkl'
    if os.path.exists(cache):
        with open(cache, 'rb') as f:
            level1 = pickle.load(f)
    else:
        level1 = []
        for key, mu, B in census_rules():
            per = {}
            for m, m2 in SHAPES:
                sets = shape_sets(mu, m, m2)
                if sets:
                    per[(m, m2)] = sets
            double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
            level1.append((key, mu, [sorted(b) for b in B], double, per))
        with open(cache, 'wb') as f:
            pickle.dump(level1, f)
    stats = {}
    nopen = 0; n = 0
    for idx, (key, mu, B, double, per) in enumerate(level1):
        if not double or not per:
            continue
        n += 1
        res = residuals([F for sets in per.values() for F in sets])
        memo = {}
        outs = []
        for R in res:
            used, bad = close(mu, frozenset(R), memo)
            outs.append('%s:%s' % (','.join(sorted(R)), '+'.join(used) if used else 'OPEN@' + ','.join(sorted(bad))))
        if any('OPEN' in o for o in outs):
            nopen += 1
        tag = (key[0], 'I%d' % len(per), tuple(sorted('%s%s' % (M[m] or '1', M[m2]) for m, m2 in per)), tuple(outs))
        stats.setdefault(tag, []).append(key)
        if idx % 100 == 0:
            print('progress', idx, file=sys.stderr, flush=True)
    for tag in sorted(stats, key=str):
        print(len(stats[tag]), tag, 'eg', stats[tag][0], flush=True)
    print('rules with a two-site move', n, 'open', nopen)
