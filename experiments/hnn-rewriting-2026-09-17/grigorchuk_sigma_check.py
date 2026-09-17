"""Check Lysenok's substitution sigma: a->aca, b->d, c->b, d->c on the relators (ad)^4, (adacac)^4
of the first Grigorchuk group acting on level n of the binary tree:
a = eps, b = (a, c), c = (a, d), d = (1, b). A wrong substitution is a control."""
n = 14
def gens(m):
    if m == 0:
        return {g: [0] for g in 'abcd'}
    G = gens(m - 1); h = 1 << (m - 1)
    I = list(range(h))
    sec = lambda x, y: [G[x][v] if x else v for v in I] + [h + (G[y][v] if y else v) for v in I]
    return {'a': [h + v for v in I] + I, 'b': sec('a', 'c'), 'c': sec('a', 'd'), 'd': sec(None, 'b')}
G = gens(n); N = 1 << n; ident = list(range(N))
def perm(word):
    p = list(range(N))
    for c in word:
        g = G[c]; p = [g[x] for x in p]
    return p
subst = lambda w, s: ''.join(s[c] for c in w)
rels = ['aa', 'bb', 'cc', 'dd', 'bcd', 'ad' * 4, 'adacac' * 4]
print('relators trivial at level', n, [perm(r) == ident for r in rels], ' (ad)^2 trivial:', perm('ad' * 2) == ident)
for name, s in [('Lysenok a->aca b->d c->b d->c', dict(a='aca', b='d', c='b', d='c')),
                ('control a->aca b->c c->d d->b', dict(a='aca', b='c', c='d', d='b'))]:
    res = []
    for r in rels[5:]:
        w = r
        for k in range(1, 4):
            w = subst(w, s); res.append(perm(w) == ident)
    print(name, 'sigma^k(r)=1 for r in (ad)^4,(adacac)^4, k=1..3:', res)
