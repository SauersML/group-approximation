# Independent checker for Klein-chain certificates of non-left-orderability of a BMW parity kernel.
# usage: verify_klein.py census.json chains.json [--trace]
# chains.json: {"<class>": ["v..|h..", ...], ...} listing x_1, ..., x_m.  For each class it checks
#  1. the squares form a VH-datum and the rewriting system {xx -> 1, h v -> v' h'} is locally confluent,
#     so every element has a unique normal form (V-word)(H-word) (Newman's lemma);
#  2. each x_i is in normal form, nontrivial, and has even V- and even H-length (so x_i lies in Gamma^+);
#  3. x_{i+1} x_i x_{i+1}^-1 x_i = 1 for all i (indices mod m), i.e. x_{i+1} inverts x_i.
# Lemma: in a left-ordered group, a b a^-1 = b^-1 with b != 1 implies |b| < |a|, where |g| = max(g, g^-1).
# Hence |x_1| < |x_2| < ... < |x_m| < |x_1|, so Gamma^+ is not left-orderable.
# Uses only the census file; shares no code with the search.
import json, sys
D = json.load(open(sys.argv[1])); CH = json.load(open(sys.argv[2])); TRACE = '--trace' in sys.argv
m, n = D['m'], D['n']      # m horizontal letters, n vertical letters; all involutions
assert D['pA'] == 0 and D['pB'] == 0
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
                if x == y and a == b:
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
            v2, h2 = SQ[(h, v)]
            assert nf([('h', h), ('v', v2), ('h', h2)]) == ((v,), ())
            assert nf([('v', v2), ('h', h2), ('v', v)]) == ((), (h,))
    def parse(s):
        a, b = s.split('|')
        return tuple(int(c) for c in a[1:]), tuple(int(c) for c in b[1:])
    def word(g): return [('v', a) for a in g[0]] + [('h', a) for a in g[1]]
    def invw(g): return [('h', a) for a in reversed(g[1])] + [('v', a) for a in reversed(g[0])]
    X = [parse(s) for s in chain]
    for g in X:
        assert g != ((), ()) and nf(word(g)) == g
        assert len(g[0]) % 2 == 0 and len(g[1]) % 2 == 0
    for i in range(len(X)):
        b, a = X[i], X[(i + 1) % len(X)]
        tr = [show(word(a) + word(b) + invw(a) + word(b))]
        assert nf(word(a) + word(b) + invw(a) + word(b), tr) == ((), ()), (ci, i)
        if TRACE: print('  %s inverts %s:\n    ' % (chain[(i + 1) % len(X)], chain[i]) + '\n    = '.join(tr))
def show(w): return ' '.join(x + str(a) for x, a in w) or '1'
for c, chain in CH.items():
    check(int(c), chain)
    print('class', c, 'Klein chain of length', len(chain), 'verified: Gamma^+ is not left-orderable', flush=True)
