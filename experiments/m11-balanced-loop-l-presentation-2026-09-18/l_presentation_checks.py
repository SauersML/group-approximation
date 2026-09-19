#!/usr/bin/env python3
"""Checks for the exact finite L-presentation of the balanced-loop host R° = <M_11, b, C>.

Points are coded 0..10 here (point x+1 in the node).  Run: python3 l_presentation_checks.py
  1. letter sections never raise weight; weight-preserving letter/point pairs;
  2. b has order 55, C^k != 1 for 0 < k <= 60;
  3. explicit words sigma(s) for iota_0(s), s in {alpha, beta, b, C}, verified exactly;
  4. the identities [C, pi_1] = C@5 * (C^-1)@6 and C = pi^-1 [C,pi_1] pi * (b alpha)@4 (0-based);
  5. the weight-descent tree of the exactness proof, run on sample relators.
"""
import heapq, random, sys
sys.setrecursionlimit(10000)
from rgroup import (D, ID, PERMS, IDX, WORD, PINV, ROOT, SEC, pmul, pinv, pm, nf, inv, mul,
                    weight, root, sections, is_trivial, conj, comm, power, perm_nf)

def show(*a): print(*a, flush=True)
def is_perm_only(w): return all(isinstance(t, int) for t in w)
def perm_of(w): return root(w)

# ---- 1. weight facts
show('== 1. letter sections')
pres = []
for l in 'bBCc':
    for x in range(D):
        s = SEC[l].get(x, '')
        wt = weight(nf(s))
        assert wt <= 1
        if wt == 1: pres.append((l, x, s))
show('weight-preserving (letter, point, section):', pres)
show('C/c at 4 gives b-letter (C-count drops); b/B only preserve at 0; C/c only at 3,4,5')

# ---- 2. orders
show('== 2. orders')
bw = nf('b'); Cw = nf('C')
ob = [k for k in range(1, 200) if is_trivial(power(bw, k))]
show('b^k = 1 for k < 200:', ob)
show('C^k = 1 for 0<k<=60:', [k for k in range(1, 61) if is_trivial(power(Cw, k))])

# ---- 3a. single-point commutators [b, b^g]
show('== 3. sigma words')
def single_point(w):
    """If root(w)=1 and exactly one section is nontrivial, return (z, section nf)."""
    if root(w) != 0: return None
    secs = sections(w)
    nz = [(x, s) for x, s in enumerate(secs) if not is_trivial(s)]
    return nz[0] if len(nz) == 1 else None

cands = []
for gi in range(1, len(PERMS)):
    p = PERMS[gi]
    img = {p[0], p[1], p[2]}
    if len(img & {0, 1, 2}) != 1: continue
    w = comm(bw, conj(bw, perm_nf(p)))
    sp = single_point(w)
    if sp and is_perm_only(sp[1]):
        cands.append((sp[0], perm_of(sp[1]), gi, w))
show('single-point perm commutators [b,b^g]: found', len(cands),
     'points', sorted({c[0] for c in cands}))
z0, c0, g0, w0 = cands[0]
show('example: z=%d, section perm index %d, weight %d' % (z0, c0, weight(w0)))

# move to point 0: tau with z^tau = 0
def tau_to(z, t):
    """a perm index mapping z -> t"""
    for i, p in enumerate(PERMS):
        if p[z] == t: return i
TAU = [tau_to(0, x) for x in range(D)]      # 0 -> x
gens0 = {}   # perm index c -> word for iota_0(c), minimal weight
for (z, c, gi, w) in cands:
    t = tau_to(z, 0)
    ww = conj(w, nf([t]))
    if c not in gens0 or weight(ww) < weight(gens0[c]): gens0[c] = ww
show('distinct iota_0 generators from commutators:', len(gens0))
# conjugators iota_0(alpha), iota_0(beta) realized by b^h (alpha at 1, beta at 2)
bconj = {}
for l, pt in (('a', 1), ('e', 2)):
    h = tau_to(pt, 0)
    bconj[l] = conj(bw, nf([h]))            # section at 0 is alpha (resp. beta)
    assert perm_of(sections(bconj[l])[0]) == ROOT[l]
# enlarge: iota_0(c^u) for u a short word in a,e, via b^h conjugation
level = dict(gens0)
for rnd in range(2):
    new = {}
    for c, w in level.items():
        for l in 'ae':
            cu = pmul(pmul(PINV[ROOT[l]], c), ROOT[l])
            ww = conj(w, bconj[l])
            if cu not in gens0 and cu not in new: new[cu] = ww
    gens0.update(new); level = new
show('iota_0 generator pool size:', len(gens0))
# Dijkstra in M_11 with cost = weight
dist = {0: 0}; word = {0: ()}; pq = [(0, 0)]
while pq:
    d, u = heapq.heappop(pq)
    if d > dist[u]: continue
    for c, w in gens0.items():
        for cc, ww in ((c, w), (PINV[c], inv(w))):
            v = pmul(u, cc); nd = d + weight(ww)
            if v not in dist or nd < dist[v]:
                dist[v] = nd; word[v] = word[u] + (ww,); heapq.heappush(pq, (nd, v))
assert len(dist) == 7920
show('iota_0(M_11): all 7920 elements reached; max weight', max(dist.values()))
def iota0_perm(i): return mul(*word[i])
SIG = {}
SIG['a'] = iota0_perm(ROOT['a']); SIG['e'] = iota0_perm(ROOT['e'])
SIG['A'] = inv(SIG['a']); SIG['E'] = inv(SIG['e'])

def iota(x, w):
    """word for iota_x(w) given word w0 for iota_0: tau^-1 w0 tau, 0^tau = x"""
    return conj(w, nf([TAU[x]]))
def letters(w):
    out = []
    for t in w:
        if isinstance(t, int): out.extend(WORD[PERMS[t]])
        else: out.append(t)
    return out
def sigma(w):
    return mul(*[SIG[l] for l in letters(w)])

SIG['b'] = mul(bw, inv(iota(2, SIG['e'])), inv(iota(1, SIG['a'])))
SIG['B'] = inv(SIG['b'])

def check_iota0(w, s):
    """exact: w = iota_0(s) in R° (root 1, section 0 equals s, others 1)"""
    if root(w) != 0: return False
    secs = sections(w)
    if not is_trivial(mul(secs[0], inv(s))): return False
    return all(is_trivial(secs[x]) for x in range(1, D))

# ---- 4. pi_1, pi and the C identities
show('== 4. C identities')
def first_perm(pred):
    for p in sorted(PERMS, key=lambda q: (len(WORD[q]), WORD[q])):
        if pred(p): return p
P1 = first_perm(lambda p: p[3] == 3 and p[4] == 4 and p[5] == 6)
PI = first_perm(lambda p: p[5] == 3 and p[6] == 5)
show('pi_1 =', WORD[P1], ' pi =', WORD[PI], '(a = alpha, e = beta)')
p1w, piw = perm_nf(P1), perm_nf(PI)
cC = inv(Cw)
lhs = comm(Cw, p1w)
secs = sections(lhs)
ok1 = root(lhs) == 0 and is_trivial(mul(secs[5], cC)) and is_trivial(mul(secs[6], Cw)) \
      and all(is_trivial(secs[x]) for x in range(D) if x not in (5, 6))
show('[C,pi_1] = C@5 (C^-1)@6 :', ok1)
rhs = mul(conj(lhs, piw), inv(iota(4, mul(SIG['b'], SIG['a']))))   # candidate for iota_3(C) iota_5(C^-1)
show('C = pi^-1[C,pi_1]pi (b alpha)@4 :', is_trivial(mul(inv(Cw), conj(lhs, piw), iota(4, mul(SIG['b'], SIG['a'])))))

for l in 'aeb':
    show('sigma(%s): weight %d, tokens %d, exact iota_0 check: %s'
         % (l, weight(SIG[l]), len(SIG[l]), check_iota0(SIG[l], nf(l))))

# iota_0(C) = iota_0(pi)^-1 (C^g)^-1 iota_0(pi_1)^-1 C^g iota_0(pi_1) iota_0(pi) * sigma(iota_4(b alpha)), 3^g = 0
g3 = perm_nf(PERMS[tau_to(3, 0)])
Cg = conj(Cw, g3)
s_p1, s_pi = sigma(p1w), sigma(piw)
inner = mul(inv(Cg), inv(s_p1), Cg, s_p1)
SIG['C'] = mul(inv(s_pi), inner, s_pi, sigma(iota(4, mul(SIG['b'], SIG['a']))))
SIG['c'] = inv(SIG['C'])
show('sigma(C): weight %d, tokens %d' % (weight(SIG['C']), len(SIG['C'])))
show('sigma(C) exact iota_0 check:', check_iota0(SIG['C'], Cw))

# ---- 5. weight descent
show('== 5. weight descent of the exactness proof')
def is_leaf(w):
    if weight(w) == 0: return True
    if all(t == 'b' for t in w) or all(t == 'B' for t in w):
        return len(w) % 55 == 0
    return False
_DT = {}
def descent(w, depth=0):
    """returns (#nodes, height) of the descent tree of a relator w; raises if a leaf is bad"""
    if w in _DT: return _DT[w]
    if depth > 400: raise RuntimeError('no termination')
    if is_leaf(w):
        assert root(w) == 0, 'leaf not a relator'
        _DT[w] = (1, 0); return _DT[w]
    assert root(w) == 0, 'node has nontrivial root'
    n, h = 1, 0
    for s in sections(w):
        if s:
            assert weight(s) <= weight(w)
            a, b_ = descent(s, depth + 1); n += a; h = max(h, b_ + 1)
    _DT[w] = (n, h); return _DT[w]

samples = {}
samples['b^55'] = power(bw, 55)
samples['R2(b)'] = mul(inv(bw), SIG['b'], iota(1, SIG['a']), iota(2, SIG['e']))
samples['R2(C)'] = mul(inv(Cw), iota(3, SIG['C']), iota(4, mul(SIG['b'], SIG['a'])), iota(5, SIG['c']))
samples['[C,pi_1]C@6c@5'] = mul(lhs, iota(6, SIG['C']), iota(5, SIG['c']))
samples['[iota_1(b),iota_3(C)]'] = comm(iota(1, SIG['b']), iota(3, SIG['C']))
samples['[sigma(b),h]'] = comm(SIG['b'], perm_nf(PERMS[tau_to(1, 2)]) if PERMS[tau_to(1, 2)][0] == 0 else
                               perm_nf(first_perm(lambda p: p[0] == 0 and p[1] == 2)))
samples['C2 sec0(sigma(C)) C^-1'] = mul(sections(SIG['C'])[0], cC)
samples['sigma(R2(b))'] = sigma(samples['R2(b)'])
random.seed(1)
for i in range(4):
    u = nf(''.join(random.choice('aAeEbBCc') for _ in range(14)))
    for (z, c, gi, w) in cands[:1]:
        pass
    # u w u^-1 w^-1 style relator: [u, v] where v commutes with u is rare; use u r u^-1 with r = R2(C)
    samples['conj R2(C) #%d' % i] = mul(u, samples['R2(C)'], inv(u))
for name, w in samples.items():
    assert is_trivial(w), name
    n, h = descent(w)
    show('%-26s weight %5d  descent nodes %6d  height %3d' % (name, weight(w), n, h))
show('all descent trees finite, leaves = weight-0 relators or b^{55j}')

# ---- 5b. relators with deep descent trees: u^n for torsion words u
show('== 5b. torsion relators u^n (n = order of u)')
random.seed(7)
found = 0; tries = 0
while found < 12 and tries < 400:
    tries += 1
    L = random.choice([2, 3, 4])
    u = nf(''.join(random.choice('aebBCc') if i % 2 else random.choice('ae') for i in range(2 * L)))
    if weight(u) == 0: continue
    cur = u; n = 1
    while n <= 330 and not is_trivial(cur):
        cur = mul(cur, u); n += 1
    if n > 330: continue
    r = power(u, n)
    nd, h = descent(r)
    found += 1
    show('u=%-12s order %4d  weight(u^n) %5d  descent nodes %6d  height %3d'
         % (''.join(t if isinstance(t, str) else '.' for t in u), n, weight(r), nd, h))
show('all descent trees finite, leaves = weight-0 relators or b^{55j}')

# ---- 6. the finite set Q_0: base relators and their closure under letterwise sections
show('== 6. Q_0 = section closure of the base relators (raw words, free reduction only)')
LP = {l: PERMS[ROOT[l]] for l in 'aAeE'}
def fred(s):
    st = []
    for ch in s:
        if st and st[-1] == INV1[ch]: st.pop()
        else: st.append(ch)
    return ''.join(st)
INV1 = {'a': 'A', 'A': 'a', 'e': 'E', 'E': 'e', 'b': 'B', 'B': 'b', 'C': 'c', 'c': 'C'}
def rsec(s, x):
    p = x; out = []
    for ch in s:
        if ch in LP: p = LP[ch][p]
        else: out.append(SEC[ch].get(p, ''))
    return fred(''.join(out))
def rword(w): return fred(''.join(letters(w)))
def rw(*ws): return fred(''.join(rword(w) for w in ws))
stab1 = []   # two generators of Stab_{M_11}(point 0) ~ M_10
import itertools
for p in sorted(PERMS, key=lambda q: len(WORD[q])):
    if p[0] == 0 and p != ID: stab1.append(p)
# pick a generating pair of the point stabilizer (order 720)
def gen_order(gs):
    seen = {ID}; fr = [ID]
    while fr:
        nx = []
        for u in fr:
            for g in gs:
                v = pm(u, g)
                if v not in seen: seen.add(v); nx.append(v)
        fr = nx
    return len(seen)
H = None
for g1, g2 in itertools.combinations(stab1[:60], 2):
    if gen_order([g1, g2]) == 720: H = [g1, g2]; break
show('Stab(1) generators:', [WORD[h] for h in H])
base = {}
base['b^55'] = 'b' * 55
base['R2b'] = rw(inv(bw), SIG['b'], iota(1, SIG['a']), iota(2, SIG['e']))
base['R2C'] = rw(inv(Cw), iota(3, SIG['C']), iota(4, mul(SIG['b'], SIG['a'])), iota(5, SIG['c']))
for s in 'aebC':
    for t in 'aebC':
        base['R3 %s%s' % (s, t)] = rw(comm(SIG[s], iota(1, SIG[t])))
    for j, h in enumerate(H):
        base['R4 %s%d' % (s, j)] = rw(comm(SIG[s], perm_nf(h)))
    sw = rword(SIG[s])
    base['C2 %s@1' % s] = fred(rsec(sw, 0) + INV1[s])
    for x in range(1, D):
        base['C2 %s@%d' % (s, x + 1)] = rsec(sw, x)
base = {k: v for k, v in base.items() if v}
for k, v in base.items():
    assert is_trivial(nf(v)), k
show('base relators (nonempty):', len(base), ' max length', max(map(len, base.values())))
Q0 = set(base.values()); fr = list(Q0)
while fr:
    s = fr.pop()
    for x in range(D):
        t = rsec(s, x)
        if t and t not in Q0: Q0.add(t); fr.append(t)
show('|Q_0 minus R1| =', len(Q0), ' max length', max(map(len, Q0)),
     ' total letters', sum(map(len, Q0)))
show('every element of Q_0 is trivial in R°:', all(is_trivial(nf(q)) for q in Q0))
