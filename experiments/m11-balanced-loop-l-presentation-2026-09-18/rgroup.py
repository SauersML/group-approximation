#!/usr/bin/env python3
"""Exact arithmetic in the balanced-loop host R° = <M_11, b, C> (X = {1..11} coded 0..10).

Right actions: (x w)^g = x^{pi_g} w^{g|_x};  (gh)|_x = g|_x h|_{x^{pi_g}}.
  alpha = (1,...,11),  beta = (1,2,3,4,8)(5,10,7,11,6),  <alpha, beta> = M_11;
  b = (b, alpha, beta, 1, ..., 1)                 (trivial root);
  C = (1, 1, 1, C, b alpha, C^-1, 1, ..., 1)      (trivial root).
Letters: a/A = alpha^{+-1}, e/E = beta^{+-1}, b/B = b^{+-1}, C/c = C^{+-1}.

Normal form ("nf"): a tuple of tokens, each either an int (index of a non-identity
element of M_11) or one of the non-rooted letters 'b','B','C','c'; freely reduced, with
maximal rooted runs merged.  The WEIGHT of an nf is its number of letter tokens.

Since b and C have trivial root permutation, the section of an nf at x is the
concatenation of the letter sections read at points x^{(product of the perm tokens so far)}.
Exact word problem: g = 1 iff every nf reachable by taking sections has trivial root
(the reachable set is finite: weights never increase and M_11 is finite).
"""
D = 11
ID = tuple(range(D))
ALPHA = tuple((x + 1) % D for x in range(D))
def cyc(*cs):
    p = list(range(D))
    for c in cs:
        for i in range(len(c)):
            p[c[i] - 1] = c[(i + 1) % len(c)] - 1
    return tuple(p)
BETA = cyc((1, 2, 3, 4, 8), (5, 10, 7, 11, 6))
def pm(p, q): return tuple(q[p[x]] for x in range(D))      # first p, then q
def pinv(p):
    r = [0] * D
    for x in range(D): r[p[x]] = x
    return tuple(r)

# enumerate M_11 with shortest positive words in a, e
PERMS = [ID]; WORD = {ID: ''}; IDX = {ID: 0}
_fr = [ID]
while _fr:
    nx = []
    for p in _fr:
        for n, g in (('a', ALPHA), ('e', BETA)):
            q = pm(p, g)
            if q not in IDX:
                IDX[q] = len(PERMS); PERMS.append(q); WORD[q] = WORD[p] + n; nx.append(q)
    _fr = nx
assert len(PERMS) == 7920
MUL = {}
def pmul(i, j):
    k = (i, j)
    r = MUL.get(k)
    if r is None:
        r = IDX[pm(PERMS[i], PERMS[j])]; MUL[k] = r
    return r
PINV = [IDX[pinv(p)] for p in PERMS]
ROOT = {'a': IDX[ALPHA], 'A': IDX[pinv(ALPHA)], 'e': IDX[BETA], 'E': IDX[pinv(BETA)]}
INVL = {'b': 'B', 'B': 'b', 'C': 'c', 'c': 'C', 'a': 'A', 'A': 'a', 'e': 'E', 'E': 'e'}
# sections of non-rooted letters: point -> raw word
SEC = {'b': {0: 'b', 1: 'a', 2: 'e'}, 'B': {0: 'B', 1: 'A', 2: 'E'},
       'C': {3: 'C', 4: 'ba', 5: 'c'}, 'c': {3: 'c', 4: 'AB', 5: 'C'}}

def nf(raw):
    """Normalize a raw word (str/iterable of letters, ints allowed as perm tokens)."""
    st = []
    for t in raw:
        if isinstance(t, str) and t in ROOT: t = ROOT[t]
        if isinstance(t, int):
            if t == 0: continue
            if st and isinstance(st[-1], int):
                m = pmul(st.pop(), t)
                if m: st.append(m)
            else: st.append(t)
        else:
            if st and st[-1] == INVL[t]:
                st.pop()
                if len(st) >= 2 and isinstance(st[-1], int) and isinstance(st[-2], int):
                    m = pmul(st[-2], st[-1]); st.pop(); st.pop()
                    if m: st.append(m)
            else: st.append(t)
    return tuple(st)

def inv(w): return tuple(PINV[t] if isinstance(t, int) else INVL[t] for t in reversed(w))
def mul(*ws): return nf(t for w in ws for t in w)
def weight(w): return sum(1 for t in w if not isinstance(t, int))
def root(w):
    r = 0
    for t in w:
        if isinstance(t, int): r = pmul(r, t)
    return r

def sections(w):
    """Return list of the 11 section nfs of nf w."""
    out = []
    for x in range(D):
        p = x; raw = []
        for t in w:
            if isinstance(t, int): p = PERMS[t][p]
            else:
                s = SEC[t].get(p)
                if s: raw.append(s)
        out.append(nf(''.join(raw)))
    return out

_TRIV = {}
def is_trivial(w, limit=10 ** 6):
    """Exact: w = 1 in R° iff all reachable sections have trivial root."""
    if w in _TRIV: return _TRIV[w]
    seen = {w}; stack = [w]
    while stack:
        u = stack.pop()
        if root(u) != 0:
            _TRIV[w] = False; return False
        for s in sections(u):
            if s and s not in seen:
                seen.add(s); stack.append(s)
                if len(seen) > limit: raise RuntimeError('limit')
    _TRIV[w] = True
    return True

def conj(w, g): return mul(inv(g), w, g)            # w^g = g^-1 w g
def comm(u, v): return mul(inv(u), inv(v), u, v)    # [u,v] = u^-1 v^-1 u v
def power(w, k): return mul(*([w] * k)) if k >= 0 else power(inv(w), -k)
def perm_nf(p): return nf([IDX[p]])
