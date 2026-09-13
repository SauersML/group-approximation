import ast, itertools, pickle
from tp import M, rule
from census_moves import residuals
from level2 import mul, inv
from level2b import GEOM, PATTERNS, model
# For the example rule of every row of level2b.txt: the closing step for every pattern P over every residual,
# with one explicit move, replayed by direct evaluation of all touched windows (assertions).
def name(w, r):
    orders, img, names = model(r)
    letter = {v: k for k, v in names.items()}
    out = []
    for g, e in w:
        if orders[g] and e > orders[g] // 2:
            e -= orders[g]
        out.append(letter[g] + ('' if e == 1 else '^%d' % e))
    return ' '.join(out) or '1'
def find(mu, r, allowed):
    S, winsites, tors = GEOM[r]
    equal = [(u, w) for u, w, lab in tors if lab not in allowed]
    for ch in itertools.product([(x, y) for x in range(3) for y in range(3) if x != y], repeat=len(S)):
        x0 = {s: c[0] for s, c in zip(S, ch)}; x1 = {s: c[1] for s, c in zip(S, ch)}
        def bt(i):
            if i == len(winsites):
                return True
            g, st = winsites[i]
            free = [w for w in dict.fromkeys(st) if w not in x0]
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
            return x0, x1, equal
    return None
def replay(mu, r, move):
    x0, x1, equal = move
    orders, img, _ = model(r)
    S = GEOM[r][0]
    for s in S:
        assert x0[s] != x1[s]
    for g in {mul(s, inv(img[n], orders), orders) for s in S for n in M}:
        st = [mul(g, img[n], orders) for n in M]
        assert mu[tuple(x0[w] for w in st)] == mu[tuple(x1[w] for w in st)], (r, g)
    for u, w in equal:
        assert x0[u] == x0[w]
    return len({mul(s, inv(img[n], orders), orders) for s in S for n in M})
if __name__ == '__main__':
    with open('level1_rows.pkl', 'rb') as f:
        level1 = {key: per for key, mu, B, double, per in pickle.load(f)}
    for line in open('level2b.txt'):
        if ' eg ' not in line:
            continue
        key = ast.literal_eval(line.rsplit(' eg ', 1)[1].strip())
        mu = rule(*key)
        print('rule', key, 'row', line.split(' eg ')[0].split(' ', 1)[1])
        memo = {}
        for R in residuals([F for sets in level1[key].values() for F in sets]):
            for P in PATTERNS:
                if not R <= P:
                    continue
                step = None
                for r in sorted(P):
                    if r[1] == '2':
                        allowed = frozenset('%s2' % e for e in 'abc' if e != r[0])
                        memo.setdefault((r, allowed), find(mu, r, allowed))
                        if memo[(r, allowed)]:
                            step = (r, allowed); break
                if step is None:
                    for r in sorted(P):
                        if r[1] == '3':
                            allowed = frozenset('%s2' % e for e in 'abc' if e != r[0]) - P
                            memo.setdefault((r, allowed), find(mu, r, allowed))
                            if memo[(r, allowed)]:
                                step = (r, allowed); break
                print('  residual %s pattern %s: %s' % (','.join(sorted(R)) or '-', ','.join(sorted(P)),
                      '%s-%s, e2 pairs forced equal for %s' % (step[0][0], 'swap' if step[0][1] == '2' else 'cycle',
                      ','.join(sorted({'a2', 'b2', 'c2'} - {step[0][0] + '2'} - step[1])) or 'none') if step else 'OPEN'))
        for (r, allowed), move in sorted(memo.items(), key=str):
            if not move:
                continue
            nw = replay(mu, r, move)
            x0, x1, equal = move
            S = GEOM[r][0]
            print('    move %s-%s (e2 equal: %s): change %s | context %s | %d windows replayed' % (
                r[0], 'swap' if r[1] == '2' else 'cycle', ','.join(sorted({'a2', 'b2', 'c2'} - {r[0] + '2'} - allowed)) or 'none',
                ' '.join('%s:%d->%d' % (name(s, r), x0[s], x1[s]) for s in S),
                ' '.join('%s=%d' % (name(w, r), v) for w, v in x0.items() if w not in S), nw))
