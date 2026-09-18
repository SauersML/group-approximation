# Independent checker for Klein-chain certificates of non-left-orderability of a BMW parity kernel, for
# census patterns mpA_npB with transposed letter pairs (x^-1 = iA[x] resp. iB[x]) as well as involutions.
# usage: verify_klein2.py census.json chains.json [--trace]
# chains.json: {"<class>": {"chain": ["v..|h..", ...], "roots": {"<i>": "v..|h..", ...}}, ...} listing
# x_1, ..., x_m (0-based step i goes from x_i to x_{i+1}); a bare list is allowed when there are no roots.
# For each class it checks
#  1. iA, iB are involutive permutations; the squares SQ(h, v) = (v', h') (meaning h v = v' h') form a
#     bijection {(h, v)} -> {(v, h)}; the rewriting system {x x^-1 -> 1, h v -> v' h'} is locally
#     confluent (overlaps h h^-1 v and h v v^-1), so every element has a unique normal form
#     (reduced V-word)(reduced H-word) (terminating: each rule shortens or removes an h-before-v pair);
#  2. each x_i is a nonempty normal form with even V- and even H-length, so x_i is a nontrivial element
#     of Gamma^+;
#  3. for each i (indices mod m) either (K) x_{i+1} x_i x_{i+1}^-1 x_i reduces to 1, i.e. x_{i+1} inverts x_i,
#     or (P) x_{i+1}^-1 x_i^e reduces to 1 for some |e| >= 2, i.e. x_{i+1} = x_i^e,
#     or (R) a root r (a normal form of even V- and H-length) is given for step i and x_i = r^e, x_{i+1} = r^f
#     with 1 <= |e| < |f|;  and at least one step is (K).
# In a left-ordered group with |g| = max(g, g^-1): (K) a b a^-1 = b^-1, b != 1, implies |b| < |a|;
# (P) |b| <= |b^e| for e != 0; (R) |r^e| <= |r^f| for 1 <= |e| <= |f|.  Hence |x_1| < |x_1|, so Gamma^+ is not
# left-orderable.  Uses only the census file.
import json, sys
D = json.load(open(sys.argv[1])); CH = json.load(open(sys.argv[2])); TRACE = '--trace' in sys.argv
m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
assert sorted(iA) == list(range(m)) and all(iA[iA[x]] == x for x in range(m))
assert sorted(iB) == list(range(n)) and all(iB[iB[x]] == x for x in range(n))
assert sum(iA[x] != x for x in range(m)) == 2 * D['pA'] and sum(iB[x] != x for x in range(n)) == 2 * D['pB']
INV = {'h': iA, 'v': iB}
def show(w): return ' '.join(x + str(a) for x, a in w) or '1'
def check(ci, chain):
    SQ = {tuple(a): tuple(b) for a, b in D['reps'][ci]}          # (h, v) -> (v', h'):  h v = v' h'
    assert sorted(SQ) == [(h, v) for h in range(m) for v in range(n)]
    assert sorted(SQ.values()) == [(v, h) for v in range(n) for h in range(m)]
    def nf(word, trace=None):
        w = list(word); changed = True
        while changed:
            changed = False
            for i in range(len(w) - 1):
                (x, a), (y, b) = w[i], w[i + 1]
                if x == y and INV[x][a] == b:
                    del w[i:i + 2]; changed = True
                elif x == 'h' and y == 'v':
                    v2, h2 = SQ[(a, b)]; w[i], w[i + 1] = ('v', v2), ('h', h2); changed = True
                if changed:
                    if trace is not None: trace.append(show(w))
                    break
        vs = tuple(a for x, a in w if x == 'v'); hs = tuple(a for x, a in w if x == 'h')
        assert [x for x, _ in w] == ['v'] * len(vs) + ['h'] * len(hs)
        return vs, hs
    for h in range(m):
        for v in range(n):
            v3, h3 = SQ[(iA[h], v)]                                   # overlap h h^-1 v
            assert nf([('h', h), ('v', v3), ('h', h3)]) == ((v,), ())
            v2, h2 = SQ[(h, v)]                                       # overlap h v v^-1
            assert nf([('v', v2), ('h', h2), ('v', iB[v])]) == ((), (h,))
    def parse(s):
        a, b = s.split('|')
        return tuple(int(c) for c in a[1:]), tuple(int(c) for c in b[1:])
    def word(g): return [('v', a) for a in g[0]] + [('h', a) for a in g[1]]
    def invw(g): return [('h', iA[a]) for a in reversed(g[1])] + [('v', iB[a]) for a in reversed(g[0])]
    roots = {}
    if isinstance(chain, dict): roots = {int(i): parse(r) for i, r in chain.get('roots', {}).items()}; chain = chain['chain']
    X = [parse(s) for s in chain]
    for g in X + list(roots.values()):
        assert g != ((), ()) and nf(word(g)) == g
        assert len(g[0]) % 2 == 0 and len(g[1]) % 2 == 0
    def fmtg(g): return 'v' + ''.join(map(str, g[0])) + '|h' + ''.join(map(str, g[1]))
    def power(g, k):
        w = []
        for _ in range(abs(k)): w += word(g) if k > 0 else invw(g)
        return w
    strict = 0
    for i in range(len(X)):
        b, a = X[i], X[(i + 1) % len(X)]
        rel = word(a) + word(b) + invw(a) + word(b)
        tr = [show(rel)]
        if nf(rel, tr) == ((), ()):                       # (K) a inverts b: |b| < |a|
            strict += 1
            if TRACE: print('  (K) %s inverts %s:\n    ' % (chain[(i + 1) % len(X)], chain[i]) + '\n    = '.join(tr))
            continue
        ok = False
        if i in roots:                                    # (R) b = r^e, a = r^f, 1 <= |e| < |f|: |b| <= |a|
            r = roots[i]; ex = {}
            for k in range(1, len(a[0]) + len(a[1]) + 1):
                for e in (k, -k):
                    for z, name in ((b, 'b'), (a, 'a')):
                        if name not in ex and nf(invw(z) + power(r, e)) == ((), ()): ex[name] = e
            assert 'a' in ex and 'b' in ex and abs(ex['b']) < abs(ex['a']), (ci, i, ex)
            if TRACE: print('  (R) %s = r^%d, %s = r^%d, r = %s' % (chain[i], ex['b'], chain[(i + 1) % len(X)], ex['a'], fmtg(r)))
            continue
        for k in range(2, len(a[0]) + len(a[1]) + 1):          # (P) a = b^k or b^-k, k >= 2: |b| <= |a|
            for e in (k, -k):
                rel = invw(a) + power(b, e); tr = [show(rel)]
                if nf(rel, tr) == ((), ()):
                    ok = True
                    if TRACE: print('  (P) %s = (%s)^%d:\n    ' % (chain[(i + 1) % len(X)], chain[i], e) + '\n    = '.join(tr))
                    break
            if ok: break
        assert ok, (ci, i)
    assert strict >= 1
    return strict
print('pattern m=%d pA=%d n=%d pB=%d iA=%s iB=%s' % (m, D['pA'], n, D['pB'], iA, iB))
for c, chain in CH.items():
    k = check(int(c), chain)
    print('class', c, 'chain of length', len(chain['chain'] if isinstance(chain, dict) else chain), 'with', k, 'inverting steps verified: Gamma^+ is not left-orderable', flush=True)
