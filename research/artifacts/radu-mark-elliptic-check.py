#!/usr/bin/env python3
"""Exact identities in Radu's BMW lattice used by radu-mark-survives-only-if-horizontal-group-embeds.

Gamma_R = <a,b,c,x,y,z | involutions, axax, ayay, azbz, bxbx, bycy, cxcz> is the
Zappa-Szep product V.C with V = <x,y,z>, C = <a,b,c> (BMW structure). Every element
has a unique normal form v*h (v reduced in x,y,z; h reduced in a,b,c), and products
are computed with the square table h s = s' h'. This script checks the relations the
proof uses, the local action of C at the base vertex o = C of T_v, and, as a sanity
check only, that short words of C act nontrivially on short vertical words.
"""
import itertools, json, sys

TABLE = {('a','x'):('x','a'), ('a','y'):('y','a'), ('a','z'):('z','b'),
         ('b','x'):('x','b'), ('b','y'):('y','c'), ('b','z'):('z','a'),
         ('c','x'):('z','c'), ('c','y'):('y','b'), ('c','z'):('x','c')}

def red(w):
    st = []
    for l in w:
        if st and st[-1] == l:
            st.pop()
        else:
            st.append(l)
    return tuple(st)

def push(h, v):
    """h in C, v in V (words); return (v', h') with h v = v' h'."""
    h = list(h); out = []
    for s in v:
        cur = s; newh = []
        for l in reversed(h):
            s2, l2 = TABLE[(l, cur)]
            newh.append(l2); cur = s2
        h = list(reversed(newh)); out.append(cur)
    return tuple(out), tuple(h)

def mul(g1, g2):
    v1, h1 = g1; v2, h2 = g2
    v2p, h1p = push(h1, v2)
    return (red(v1 + v2p), red(h1p + h2))

def prod(*gs):
    r = ((), ())
    for g in gs:
        r = mul(r, g)
    return r

def inv(g):
    v, h = g
    return mul(((), tuple(reversed(h))), (tuple(reversed(v)), ()))

E = ((), ())
G = {l: ((), (l,)) for l in 'abc'}
G.update({s: ((s,), ()) for s in 'xyz'})
a, b, c, x, y, z = (G[l] for l in 'abcxyz')

results = {}
def check(name, lhs, rhs):
    ok = (lhs == rhs)
    results[name] = ok
    print(('OK  ' if ok else 'FAIL'), name, lhs, rhs)
    return ok

# relators of RE1
for w in ['axax', 'ayay', 'azbz', 'bxbx', 'bycy', 'cxcz', 'aa', 'bb', 'cc', 'xx', 'yy', 'zz']:
    check('relator ' + w, prod(*(G[l] for l in w)), E)

d = mul(x, z)              # delta = xz
d2 = mul(d, d)
d4 = mul(d2, d2)
u = prod(y, d2, y)         # u = y delta^2 y
check('R1 delta a delta^-1 = b', prod(d, a, inv(d)), b)
check('R1 delta b delta^-1 = a', prod(d, b, inv(d)), a)
check('R2 a delta^2 a = delta^2', prod(a, d2, a), d2)
check('R2 b delta^2 b = delta^2', prod(b, d2, b), d2)
check('R2 c delta^2 c = delta^-2', prod(c, d2, c), inv(d2))
check('R3 y a y = a', prod(y, a, y), a)
check('R3 y b y = c', prod(y, b, y), c)
check('R4 a u a = u', prod(a, u, a), u)
check('R4 c u c = u', prod(c, u, c), u)
check('R4 b u b = u^-1', prod(b, u, b), inv(u))
check('R4 u^2 = y delta^4 y', mul(u, u), prod(y, d4, y))
results['mark (xz)^4 nontrivial in Gamma_R'] = (d4 != E)
print('mark normal form', d4)

# local action of C at o: h s C = s' C with s' the V-part of push(h, s)
loc = {}
for l in 'abc':
    loc[l] = {s: push((l,), (s,))[0][0] for s in 'xyz'}
print('local action at o', loc)
results['local action a,b trivial; c swaps x,z'] = (
    loc['a'] == {'x':'x','y':'y','z':'z'} and loc['b'] == {'x':'x','y':'y','z':'z'}
    and loc['c'] == {'x':'z','y':'y','z':'x'})

# k = x h' z lies in C for h' in C with odd number of c's (chi(h') = -1); sample check
bad = 0; tested = 0
for n in range(1, 7):
    for w in itertools.product('abc', repeat=n):
        if red(w) != w or w.count('c') % 2 == 0:
            continue
        tested += 1
        k = prod(x, ((), w), z)
        if k[0] != ():
            bad += 1
results['x h z in C for chi(h) = -1 (words <= 6)'] = (bad == 0)
print('x h z in C:', tested, 'tested,', bad, 'bad')

# sanity only: reduced h in C of length <= 6 moving some vertical word of length <= 8
def reduced_words(alph, n):
    for w in itertools.product(alph, repeat=n):
        if red(w) == w:
            yield w
Vwords = [w for m in range(0, 9) for w in reduced_words('xyz', m)]
fixers = []
for n in range(1, 7):
    for h in reduced_words('abc', n):
        if all(push(h, v)[0] == v for v in Vwords):
            fixers.append(''.join(h))
results['sanity: no C-word of length <= 6 fixes T_v to depth 8'] = (not fixers)
print('C-words of length <= 6 fixing all vertical words of length <= 8:', fixers[:10])

allok = all(results.values())
print(json.dumps(results, indent=1))
print('ALL_OK' if allok else 'SOME_FAIL')
sys.exit(0 if allok else 1)
