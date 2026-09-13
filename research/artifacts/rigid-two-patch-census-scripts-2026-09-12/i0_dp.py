import itertools, sys, time
from tp import M, I, canon, census_rules, SHAPES
from census_moves import shape_sets, minimal
from i0_path import KNOWN, AMEN, path
# Class I_0: minimal conflict sets of the three-site path move over free memory, by dynamic programming over windows.
# Relators classified amenable or breaker in KNOWN are dropped; all others are kept by label or canonical word.
def min_conflicts(mu, S, winsites):
    changed = set(S)
    sites = list(dict.fromkeys(w for g, st in winsites for w in st))
    pairs = [(u, w, KNOWN.get(canon(I(u) + w), canon(I(u) + w))) for u, w in itertools.combinations(sites, 2)]
    pairs = [p for p in pairs if p[2] not in AMEN]
    ch_pairs = [p for p in pairs if p[0] in changed or p[1] in changed]
    ctx_pairs = [p for p in pairs if p[0] not in changed and p[1] not in changed]
    first, last = {}, {}
    for t, (g, st) in enumerate(winsites):
        for w in st:
            if w not in changed:
                first.setdefault(w, t); last[w] = t
    at = {}
    for u, w, l in ctx_pairs:
        at.setdefault(max(first[u], first[w]), []).append((u, w, l))
    keep = []
    for t in range(len(winsites)):
        k = {w for w in first if first[w] <= t < last[w]}
        for u, w, l in ctx_pairs:
            if max(first[u], first[w]) > t:
                k |= {v for v in (u, w) if first[v] <= t}
        keep.append(sorted(k))
    out = set()
    changes = [(x, y) for x in range(3) for y in range(3) if x != y]
    for ch in itertools.product(changes, repeat=len(S)):
        c0 = {s: c[0] for s, c in zip(S, ch)}; c1 = {s: c[1] for s, c in zip(S, ch)}
        base = frozenset(l for u, w, l in ch_pairs
                         if not (u in changed and w in changed and (c0[u], c1[u]) == (c0[w], c1[w])))
        states = {(): [frozenset()]}
        for t, (g, st) in enumerate(winsites):
            new = {}
            for key, sets in states.items():
                val = dict(key)
                own = [w for w in dict.fromkeys(st) if w not in changed and w not in val]
                for vals in itertools.product(range(3), repeat=len(own)):
                    x = dict(val); x.update(zip(own, vals))
                    if mu[tuple(c0[w] if w in changed else x[w] for w in st)] != mu[tuple(c1[w] if w in changed else x[w] for w in st)]:
                        continue
                    add = frozenset(l for u, w, l in at.get(t, []) if x[u] != x[w])
                    lst = new.setdefault(tuple((w, x[w]) for w in keep[t]), [])
                    for F in sets:
                        G = F | add
                        if any(H <= G for H in lst):
                            continue
                        lst[:] = [H for H in lst if not G <= H]
                        lst.append(G)
            states = new
            if not states:
                break
        for sets in states.values():
            for F in sets:
                out.add(base | F)
    return minimal(out)
if __name__ == '__main__':
    stats = {}
    t0 = time.time(); n = 0
    for key, mu, B in census_rules():
        double = [(i, j) for i, j in [(0, 1), (0, 2), (1, 2)] if B[i] & B[j]]
        if not double or any(shape_sets(mu, m, m2) for m, m2 in SHAPES):
            continue
        n += 1
        parts = []
        for i, j in double:
            S, winsites, sites = path(i, j, 3 - i - j)
            sets = min_conflicts(mu, S, winsites)
            core = frozenset.intersection(*sets) if sets else frozenset()
            parts.append(((M[i] or '1') + M[j], tuple(','.join(sorted(F)) for F in sets) if sets else ('NO PATH MOVE',),
                          'in every set: ' + ','.join(sorted(core))))
        tag = (key[0], tuple(parts))
        stats.setdefault(tag, []).append(key)
        if n % 20 == 0:
            print('progress', n, round(time.time() - t0, 1), file=sys.stderr, flush=True)
    for tag in sorted(stats, key=str):
        print(len(stats[tag]), tag, 'eg', stats[tag][0], flush=True)
    print('I_0 rules', n)
