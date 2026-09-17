"""Which substitution sigma makes sigma^k([a, a^b]) = 1 in the Basilica group?
Basilica acting on binary words: a(0w)=0w, a(1w)=1 b(w); b(0w)=1w, b(1w)=0 a(w).
Elements are permutations of the 2^n words of level n."""
n = 14
def gens(m):
    if m == 0:
        return [0], [0]
    a1, b1 = gens(m - 1)
    h = 1 << (m - 1)
    a = list(range(h)) + [h + b1[v] for v in range(h)]
    b = [h + v for v in range(h)] + [a1[v] for v in range(h)]
    return a, b
A, B = gens(n)
N = 1 << n
def inv_p(p):
    q = [0] * len(p)
    for i, x in enumerate(p): q[x] = i
    return q
G = {'a': A, 'b': B, 'A': inv_p(A), 'B': inv_p(B)}
def perm(word):
    p = list(range(N))
    for c in word:
        g = G[c]; p = [g[x] for x in p]
    return p
ident = list(range(N))
inv = lambda w: ''.join(c.swapcase() for c in reversed(w))
comm = lambda u, v: u + v + inv(u) + inv(v)
def subst(w, s):
    return ''.join(s[c] if c.islower() else inv(s[c.lower()]) for c in w)
rel = comm('a', inv('b') + 'a' + 'b')
print('level', n, '[a,a^b] = 1:', perm(rel) == ident, ' [a,b] = 1:', perm(comm('a', 'b')) == ident)
for name, s in [('sigma1 a->b, b->a^2', {'a': 'b', 'b': 'aa'}), ('sigma2 a->b^2, b->a', {'a': 'bb', 'b': 'a'})]:
    w = rel; res = []
    for k in range(1, 5):
        w = subst(w, s); res.append(perm(w) == ident)
    print(name, 'sigma^k([a,a^b]) = 1 for k=1..4:', res)
