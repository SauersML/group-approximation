#!/usr/bin/env python3
"""R° = <M_11, b, C> is not finitely presented: checks for the stable-relator proof.

Points are coded 0..10 (point x+1 in the node).  Letters: a/A = alpha^{+-1}, e/E = beta^{+-1},
b/B = b^{+-1}, C/c = C^{+-1}.  Uses the exact word-problem code rgroup.py of
experiments/m11-balanced-loop-l-presentation-2026-09-18.  Run: python3 nonfp_checks.py

  1. letter sections: weight-preserving (letter, point) pairs (Lemma 2 of the proof);
  2. the C-free words W_a, W_e, W_b equal alpha@1, beta@1, b@1 exactly in R°, and their
     free sections are W_s|_1 = omega_a, omega_e, 'b' with W_a|_x = W_e|_x = empty for x != 1;
  3. theta-invariance (Lemma 3): sigma^k(alpha)|_{1^k} = omega_a as free words, k = 1, 2, 3;
  4. omega_a is cyclically reduced of syllable length 14 in A = Z/55 * Z/55, so omega_a^11 != 1;
     a finite witness in S_5;
  5. illustration on the finite L-presentation of the sibling node: the stable part of the
     section closure of Q_0 is {b^55, alpha^55, beta^55}; the level-3 map phi_3 kills Q_0 and
     sends sigma(R2C) to a nontrivial element (so sigma(Q_0) is not in <<Q_0>>), also through
     a finite quotient A_f wr (level-3 group).
"""
import os, sys, io, contextlib, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
LP_DIR = os.path.join(HERE, '..', 'm11-balanced-loop-l-presentation-2026-09-18')
sys.path.insert(0, LP_DIR)
from rgroup import D, PERMS, ROOT, SEC, IDX, nf, is_trivial, root, sections, inv, mul

def show(*a): print(*a, flush=True)
INV1 = {'a': 'A', 'A': 'a', 'e': 'E', 'E': 'e', 'b': 'B', 'B': 'b', 'C': 'c', 'c': 'C'}
LP = {l: PERMS[ROOT[l]] for l in 'aAeE'}
def fred(s):
    st = []
    for ch in s:
        if st and st[-1] == INV1[ch]: st.pop()
        else: st.append(ch)
    return ''.join(st)
def winv(s): return ''.join(INV1[c] for c in reversed(s))
def rsec(s, x):
    """free section of the raw word s at point x (letterwise, then free reduction)"""
    p = x; out = []
    for ch in s:
        if ch in LP: p = LP[ch][p]
        else: out.append(SEC[ch].get(p, ''))
    return fred(''.join(out))
def rsec_v(s, v):
    for x in v: s = rsec(s, x)
    return s
def weight(s): return sum(1 for c in s if c in 'bBCc')

# ---- 1. letter sections
show('== 1. letter sections (weight-preserving pairs)')
for l in 'bBCc':
    show(' ', l, {x + 1: s for x, s in SEC[l].items()},
         ' weight-1 sections at points', [x + 1 for x, s in SEC[l].items() if weight(s) == 1])
show('  C-count preserved only at points 4, 6; at 5 the section (b alpha)^{+-1} has no C')

# ---- 2. the C-free words W_s = s@1
show('== 2. C-free words for alpha@1, beta@1, b@1')
W = {'a': 'aeaaaaeeaeaaBBeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeaaBaaeeaeeeaeeeeBaeeaBeaaaaeeaeaaabaeeababeaeaeaeaebaBeaeaeaeaeBeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeaabaee',
     'e': 'aeaaaaeeaeaaBeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeaBBeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeabeaaaaeeaeaaaBaeeaBeaaaaeeaeaaabaeeaBBeaaaaeeaeaaaBaeeabbeaaaaeeaeaaabaeeabaaee',
     'b': 'baeeaeaeaeaaaeBeaaaaeeaeaaaBaeeaBBeaaaaeeaeaaabaeeabbeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeaBeaaaaeeaeaaaBaeeaBeaaaaeeaeaaabaeeabbeaaaaeeaeaaaBaeeaBeaaaaeeaeaaabaeeabeaaeaeeeaeaBaaeeaeeeaeeeeBaeeaBeaaaaeeaeaaabaeeababeaeaeaeaeBaBeaeaeaeaeBeaaaaeeaeaaaBaeeabeaaaaeeaeaaabaeeaabaaeeaeeeaeeeeBaeeaBeaaaaeeaeaaabaeeabbaaeea'}
for s in 'aeb': W[INV1[s]] = winv(W[s])
def is_at1(w, s):
    """exact: the word w equals s@1 in R° (trivial root, section at 1 equals s, others trivial)"""
    g = nf(w)
    if root(g) != 0: return False
    sec = sections(g)
    return is_trivial(mul(sec[0], inv(nf(s)))) and all(is_trivial(sec[x]) for x in range(1, D))
for s in 'aeb':
    assert 'C' not in W[s] and 'c' not in W[s]
    secs = {x + 1: rsec(W[s], x) for x in range(D) if rsec(W[s], x)}
    show('  W_%s: length %d, C-free, equals %s@1 exactly: %s, free sections %s'
         % (s, len(W[s]), s, is_at1(W[s], s), secs))
    assert is_at1(W[s], s)
OMEGA = {'a': rsec(W['a'], 0), 'e': rsec(W['e'], 0)}
assert rsec(W['b'], 0) == 'b'
assert all(rsec(W[s], x) == '' for s in 'ae' for x in range(1, D))
show('  omega_a =', OMEGA['a'], ' omega_e =', OMEGA['e'], ' (W_b|_1 = b exactly)')

# ---- 3. theta-invariance: sigma^k(alpha)|_{1^k} = omega_a as free words
show('== 3. sigma^k(alpha) at the vertex 1^k')
def sigma(w): return fred(''.join(W[c] for c in w))
theta = {'a': OMEGA['a'], 'e': OMEGA['e'], 'b': 'b'}
for s in 'ae': theta[INV1[s]] = winv(theta[s])
theta['B'] = 'B'
def th(w): return fred(''.join(theta[c] for c in w))
u = 'a'
for k in range(1, 4):
    u = sigma(u)
    top = rsec_v(u, [0] * k)
    show('  k=%d: len sigma^k(alpha) = %d, section at 1^k = %s, equals omega_a: %s'
         % (k, len(u), top, top == OMEGA['a']))
    assert top == OMEGA['a']
w2 = sigma(sigma('a'))
assert rsec(w2, 0) == th(sigma('a'))
assert all(rsec(th(sigma('a')), x) == rsec(sigma('a'), x) for x in range(D))
show('  checked: sigma(u)|_1 = theta(u) and theta(u)|_x = u|_x for u = sigma(alpha)')

# ---- 4. omega_a has infinite order in A = Z/55 * Z/55 (b, C -> 1)
show('== 4. omega_a in A = <a|a^55> * <e|e^55>')
def chi(w):
    """normal form of the image of w in A (b, C -> 1): list of (letter, exponent mod 55)"""
    st = []
    for ch in w:
        g = ch.lower()
        if g not in 'ae': continue
        x = 1 if ch in 'ae' else -1
        if st and st[-1][0] == g:
            n = (st[-1][1] + x) % 55; st.pop()
            if n: st.append((g, n))
        else: st.append((g, x % 55))
    return st
cw = chi(OMEGA['a'])
show('  chi(omega_a) syllables:', len(cw), cw)
assert len(cw) == 14 and cw[0][0] != cw[-1][0]          # cyclically reduced, even length
assert len(chi(OMEGA['a'] * 11)) == 14 * 11
show('  omega_a is cyclically reduced of syllable length 14, so omega_a^11 has 154 syllables != 1')
def pmul(p, q): return tuple(q[p[i]] for i in range(len(p)))   # right action: first p, then q
def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p): r[j] = i
    return tuple(r)
def pord(p):
    n, q, I = 1, p, tuple(range(len(p)))
    while q != I: q = pmul(q, p); n += 1
    return n
def fin(w, A, E):
    g = tuple(range(len(A))); tab = {'a': A, 'A': pinv(A), 'e': E, 'E': pinv(E)}
    for ch in w:
        if ch in tab: g = pmul(g, tab[ch])
    return g
A5, E5 = (1, 2, 3, 4, 0), (1, 3, 0, 4, 2)
assert pord(A5) == 5 and pord(E5) == 5
show('  S_5 witness: a -> (12345), e -> (1 2 4 5 3); image of omega_a has order',
     pord(fin(OMEGA['a'], A5, E5)))
assert pord(fin(OMEGA['a'], A5, E5)) not in (1, 11)

# ---- 5. illustration on the sibling finite L-presentation <S | Q_0 | sigma>
show('== 5. the L-presentation of m11-balanced-loop-host-has-exact-finite-l-presentation')
g = {'__name__': 'lp'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(os.path.join(LP_DIR, 'l_presentation_checks.py')).read(), g)
Q0, base = set(g['Q0']), g['base']
SIGW = {s: g['rword'](v) for s, v in g['SIG'].items()}
for s in 'aeb': assert SIGW[s] == W[s]
show('  sibling sigma words agree with W_a, W_e, W_b; |Q_0| =', len(Q0), ' letters', sum(map(len, Q0)))
Q, k = Q0, 0
while True:
    Qn = {rsec(s, x) for s in Q for x in range(D)} - {''}
    assert Qn <= Q
    if Qn == Q: break
    Q, k = Qn, k + 1
    show('  Q^(%d): %d words' % (k, len(Q)))
assert Q == {'b' * 55, 'a' * 55, 'e' * 55}
show('  stable part Q^inf = {b^55, alpha^55, beta^55}, reached at level', k)
def level_secs(w, k, first=None):
    cur = {(): w} if first is None else {(first[0],): first[1]}
    for _ in range(k - len(next(iter(cur)))):
        nxt = {}
        for v, u in cur.items():
            for x in range(D):
                s = rsec(u, x)
                if s: nxt[v + (x,)] = s
        cur = nxt
    return cur
assert all(not chi(s) for q in Q0 for s in level_secs(q, 3).values())
show('  phi_3 (level-3 sections, then chi) kills every element of Q_0')
INV = {'a': 'A', 'e': 'E', 'b': 'B', 'C': 'c'}
T0 = {}
for s in 'aebC':
    T0[s] = rsec(SIGW[s], 0); T0[INV[s]] = winv(T0[s])
q =base['R2C']
u1 = fred(''.join(T0[c] for c in q))            # sigma(R2C)|_1
show('  sigma(R2C) = W_{R2C}: its section at 1 has length', len(u1))
hits = {v: s for v, s in level_secs(u1, 3, first=(0, u1)).items() if chi(s)}
for v, s in sorted(hits.items()):
    show('   vertex', tuple(x + 1 for x in v), s, ' chi-syllables', len(chi(s)),
         ' S_5 image order', pord(fin(s, A5, E5)))
assert hits and any(pord(fin(s, A5, E5)) > 1 for s in hits.values())
show('  so phi_3(sigma(R2C)) != 1 = phi_3(<<Q_0>>): sigma(Q_0) is not contained in <<Q_0>>;')
show('  the same holds in the finite quotient (S_5)^(X^3) : (level-3 group) via a->(12345), e->(12453)')
