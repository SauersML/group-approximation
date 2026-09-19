# kverify.py rec.jsonl chain.jsonl : independent check of a Klein chain (kchain.py output) for a BMW class,
# sharing no code with the search. Uses only the squares and inverse maps of the record.
# Checks: squares are a bijection H x V -> V x H; {x x^-1 -> 1, h v -> v' h'} is locally confluent (it
# terminates, so normal forms V-word.H-word are unique); every chain element is a nontrivial normal form of
# even V- and H-length (in Gamma^+); and x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1} for every i (indices mod k).
# By Lemma 1 of bmw-40-40-193-281-332-klein-chain-proof (a b a^-1 = b^-1 with a, b in Gamma^+ - 1 forces |b| < |a|, |g| = max(g, g^-1)) this gives
# |x_0| < |x_1| < ... < |x_{k-1}| < |x_0| in any left order of Gamma^+: none exists.
import json, sys
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from vh_enum import inv_arr
r = json.loads(open(sys.argv[1]).readline()); ch = json.loads(open(sys.argv[2]).read().strip().split('\n')[-1])
assert (r['pat'], r['seed']) == (ch['pat'], ch['seed'])
m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
iA, iB = inv_arr(m, pA), inv_arr(n, pB); INV = {'h': iA, 'v': iB}
assert all(iA[iA[x]] == x for x in range(m)) and all(iB[iB[x]] == x for x in range(n))
SQ = {tuple(a): tuple(b) for a, b in r['sq']}
assert sorted(SQ) == [(h, v) for h in range(m) for v in range(n)]
assert sorted(SQ.values()) == [(v, h) for v in range(n) for h in range(m)]
def nf(word):
    w = list(word); changed = True
    while changed:
        changed = False
        for i in range(len(w) - 1):
            (x, a), (y, b) = w[i], w[i + 1]
            if x == y and INV[x][a] == b: del w[i:i + 2]; changed = True; break
            if x == 'h' and y == 'v':
                v2, h2 = SQ[(a, b)]; w[i], w[i + 1] = ('v', v2), ('h', h2); changed = True; break
    assert all(w[i][0] <= w[i + 1][0] or w[i][0] == 'v' for i in range(len(w) - 1))
    return tuple(w)
for h in range(m):
    for v in range(n):
        v2, h2 = SQ[(h, v)]
        assert nf([('h', iA[h]), ('v', v2), ('h', h2)]) == (('v', v),), (h, v)
        assert nf([('v', v2), ('h', h2), ('v', iB[v])]) == (('h', h),), (h, v)
def parse(s): return [(s[i], int(s[i + 1])) for i in range(0, len(s), 2)]
def inv(w): return [(x, INV[x][a]) for x, a in reversed(w)]
X = [nf(parse(s)) for s in ch['cycle']]; k = len(X)
for s, x in zip(ch['cycle'], X):
    assert x and list(x) == parse(s), s                       # nontrivial and already in normal form
    assert sum(c == 'v' for c, _ in x) % 2 == 0 and sum(c == 'h' for c, _ in x) % 2 == 0, s
for i in range(k):
    x, y = list(X[i]), list(X[(i + 1) % k])
    assert nf(y + x + inv(y)) == nf(inv(x)), (i, ch['cycle'][i], ch['cycle'][(i + 1) % k])
print('OK', r['pat'], 'seed', r['seed'], 'Klein chain of length', k, ch['cycle'])
