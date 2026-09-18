# bh-shell-germ: bounded search behind `tree-compatible-fixed-base-enumerations-have-infinite-index`

Evidence only; the claim node is proved by hand and does not depend on this search.

**Group searched.** H = <A, A^-1, W, W^-1, v_z : |z| <= 2> inside Thompson's V on the binary
Cantor set, with A = [0 -> 00, 10 -> 01, 11 -> 1], W = [1 -> 01, 01 -> 00, 00 -> 1] (the
near class of the order-3 generator in the normal-form enumeration of C_2*C_3), and
v_z the swap of the two children of vertex z (v_e is the root swap, the near class of
the order-2 generator). A = (v_e W)^-1, so H = <lambda(C_2*C_3), Fin_(<=2)>.

**Method.** Exact composition of prefix-replacement maps and reduced tree-pair normal
forms (for V the reduced form is unique). BFS by word length. MSI, single core, three
runs of 3 s, 283 s and 130 s, nothing left running.

**Blindness pre-check and calibration.** The planted element A v_1 A^-1 = transposition of
[01] and [1] is in H by construction. Run 1 recovered it at word length 2 (`v0.w.`,
that is v_0 W). Every generator lies in Aut(T_3), which is the invariant the claim node
identifies; the targets that the node predicts are missing are exactly the ones that
violate it, so the search tests the prediction rather than being blind to it.

**Results.**
- Runs 1 and 2: no local copy of A (on [1] or [10]) and no local A^-1 (on [11]) up to word
  length 10 complete (3.04M elements), plus 2.96M elements of length 11.
- Run 3: among the 71 transpositions of two incomparable cylinders of depth <= 3, exactly
  11 are found by length 10: the 7 sibling swaps and the 4 swaps of [b] with [b' c]
  (b' != b). These are precisely the transpositions of two branches at a common vertex of
  T_3. The other 60, and x_1, are missing.

## Script (vsearch.py, md5 882a95ed3e0c1fd358694df33d0a9ae5)
```python
# Bounded BFS in Thompson's V (binary Cantor set, prefix-replacement maps).
# Element = dict dom_prefix -> img_prefix (complete prefix codes). Exact composition, reduced normal form.
import sys, time
def norm(g):
    g = dict(g)
    changed = True
    while changed:
        changed = False
        for p in list(g):
            if p and p[-1] == '0' and p in g:
                s = p[:-1] + '1'
                if s in g:
                    q0, q1 = g[p], g[s]
                    if q0 and q1 and q0[:-1] == q1[:-1] and q0[-1] == '0' and q1[-1] == '1':
                        del g[p]; del g[s]; g[p[:-1]] = q0[:-1]; changed = True
                        break
    return frozenset(g.items())
def apply(g, x):  # g as dict, x long word
    for p, q in g.items():
        if x.startswith(p): return q + x[len(p):]
    raise ValueError('word too short: ' + x)
def compose(g, h):  # (g o h)(x) = g(h(x)); g,h frozensets
    G = dict(g); out = {}
    stack = list(dict(h).items())
    while stack:
        p, q = stack.pop()
        hit = None
        for pp in G:
            if q.startswith(pp): hit = pp; break
        if hit is not None:
            out[p] = G[hit] + q[len(hit):]
        else:
            stack.append((p + '0', q + '0')); stack.append((p + '1', q + '1'))
    return norm(out)
def inv(g): return norm({q: p for p, q in g})
def el(d): return norm(d)
ID = el({'': ''})
A = el({'0': '00', '10': '01', '11': '1'})
W = el({'1': '01', '01': '00', '00': '1'})
def swap(z): return el({**{z + '0': z + '1', z + '1': z + '0'}, **cmp_(z)})
def cmp_(z):
    d = {}
    for i in range(len(z)):
        d[z[:i] + ('1' if z[i] == '0' else '0')] = z[:i] + ('1' if z[i] == '0' else '0')
    return d
gens = {'A': A, 'a': inv(A), 'W': W, 'w': inv(W)}
for z in ['', '0', '1', '00', '01', '10', '11']:
    gens['v' + (z or 'e')] = swap(z)
B = el({'0': '0', '10': '100', '110': '101', '111': '11'})
targets = {'B': B, 'Binv': inv(B),
           'A_loc1': el({'0': '0', '100': '1000', '1010': '1001', '1011': '101', '11': '11'}),
           'Ainv_loc11': el({'0': '0', '10': '10', '1100': '110', '1101': '1110', '111': '1111'})}
# calibration: planted element inside the group, A v1 A^-1 = transposition of [01] and [1]
cal = compose(compose(A, gens['v1']), inv(A))
targets['CAL_t01_1'] = cal
tset = {v: k for k, v in targets.items()}
maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 6
cap = int(sys.argv[2]) if len(sys.argv) > 2 else 3000000
t0 = time.time()
seen = {ID: ''}; frontier = [ID]; found = {}
for L in range(1, maxlen + 1):
    nxt = []
    for g in frontier:
        wg = seen[g]
        for name, s in gens.items():
            h = compose(s, g)
            if h not in seen:
                seen[h] = name + '.' + wg
                nxt.append(h)
                if h in tset and tset[h] not in found:
                    found[tset[h]] = (L, seen[h]); print('FOUND', tset[h], L, seen[h], flush=True)
        if len(seen) > cap or time.time() - t0 > 480: break
    frontier = nxt
    print('len', L, 'new', len(nxt), 'total', len(seen), 'time', round(time.time() - t0, 1), flush=True)
    if len(seen) > cap or time.time() - t0 > 480: print('STOP budget'); break
print('DONE found', found)
```

## Transposition scan (vtrans.py) additions
```python
import itertools
def words(n): return [''.join(t) for k in range(1, n + 1) for t in itertools.product('01', repeat=k)]
def transp(x, y):
    # swap [x] and [y] (incomparable), identity elsewhere: build over a complete code refining both
    code = {''}
    def refine(code, z):
        out = set()
        for c in code:
            if z.startswith(c) and c != z:
                # split c down to z
                cur = c
                while cur != z:
                    b = z[len(cur)]
                    out.add(cur + ('1' if b == '0' else '0')); cur = cur + b
                out.add(z)
            else: out.add(c)
        return out
    code = refine(refine(code, x), y)
    d = {c: c for c in code}; d[x] = y; d[y] = x
    return norm(d)
tt = {}
for x in words(3):
    for y in words(3):
        if x < y and not x.startswith(y) and not y.startswith(x):
            tt[transp(x, y)] = (x, y)
tt[B] = ('LOCAL_A_on', '1')
maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 6
cap = int(sys.argv[2]) if len(sys.argv) > 2 else 3000000
t0 = time.time(); seen = {ID: ''}; frontier = [ID]; found = {}
for L in range(1, maxlen + 1):
    nxt = []
    for g in frontier:
        wg = seen[g]
        for name, s in gens.items():
            h = compose(s, g)
            if h not in seen:
                seen[h] = name + '.' + wg; nxt.append(h)
                if h in tt and tt[h] not in found: found[tt[h]] = (L, seen[h])
        if len(seen) > cap or time.time() - t0 > 480: break
    frontier = nxt
    print('len', L, 'total', len(seen), 'found', len(found), 'of', len(tt), round(time.time() - t0, 1), flush=True)
    if len(seen) > cap or time.time() - t0 > 480: print('STOP budget'); break
fx = sorted(found.items(), key=lambda kv: kv[1][0])
for k, v in fx: print('HIT', k, v[0], v[1])
miss = sorted(set(tt.values()) - set(found))
print('MISSING', len(miss), miss)
```

## Outputs
```
== run1
len 1 new 11 total 12 time 0.0
FOUND CAL_t01_1 2 v0.w.
len 2 new 64 total 76 time 0.0
len 3 new 281 total 357 time 0.0
len 4 new 1092 total 1449 time 0.0
len 5 new 4018 total 5467 time 0.2
len 6 new 14397 total 19864 time 1.0
len 7 new 50911 total 70775 time 3.3
DONE found {'CAL_t01_1': (2, 'v0.w.')}
== run2
len 1 new 11 total 12 time 0.0
FOUND CAL_t01_1 2 v0.w.
len 2 new 64 total 76 time 0.0
len 3 new 281 total 357 time 0.0
len 4 new 1092 total 1449 time 0.1
len 5 new 4018 total 5467 time 0.2
len 6 new 14397 total 19864 time 1.0
len 7 new 50911 total 70775 time 3.3
len 8 new 178650 total 249425 time 12.5
len 9 new 623539 total 872964 time 39.0
len 10 new 2168447 total 3041411 time 141.4
len 11 new 2958592 total 6000003 time 282.9
STOP budget
DONE found {'CAL_t01_1': (2, 'v0.w.')}
== run3
len 1 total 12 found 7 of 72 0.0
len 2 total 76 found 9 of 72 0.0
len 3 total 357 found 11 of 72 0.0
len 4 total 1449 found 11 of 72 0.0
len 5 total 5467 found 11 of 72 0.2
len 6 total 19864 found 11 of 72 0.8
len 7 total 70775 found 11 of 72 2.9
len 8 total 249425 found 11 of 72 9.6
len 9 total 872964 found 11 of 72 34.2
len 10 total 3041411 found 11 of 72 127.7
len 11 total 3100002 found 11 of 72 130.1
STOP budget
HIT ('0', '1') 1 ve.
HIT ('00', '01') 1 v0.
HIT ('10', '11') 1 v1.
HIT ('000', '001') 1 v00.
HIT ('010', '011') 1 v01.
HIT ('100', '101') 1 v10.
HIT ('110', '111') 1 v11.
HIT ('00', '1') 2 v0.W.
HIT ('01', '1') 2 v0.w.
HIT ('0', '11') 3 v1.ve.A.
HIT ('0', '10') 3 a.v0.A.
MISSING 61 [('0', '100'), ('0', '101'), ('0', '110'), ('0', '111'), ('00', '010'), ('00', '011'), ('00', '10'), ('00', '100'), ('00', '101'), ('00', '11'), ('00', '110'), ('00', '111'), ('000', '01'), ('000', '010'), ('000', '011'), ('000', '1'), ('000', '10'), ('000', '100'), ('000', '101'), ('000', '11'), ('000', '110'), ('000', '111'), ('001', '01'), ('001', '010'), ('001', '011'), ('001', '1'), ('001', '10'), ('001', '100'), ('001', '101'), ('001', '11'), ('001', '110'), ('001', '111'), ('01', '10'), ('01', '100'), ('01', '101'), ('01', '11'), ('01', '110'), ('01', '111'), ('010', '1'), ('010', '10'), ('010', '100'), ('010', '101'), ('010', '11'), ('010', '110'), ('010', '111'), ('011', '1'), ('011', '10'), ('011', '100'), ('011', '101'), ('011', '11'), ('011', '110'), ('011', '111'), ('10', '110'), ('10', '111'), ('100', '11'), ('100', '110'), ('100', '111'), ('101', '11'), ('101', '110'), ('101', '111'), ('LOCAL_A_on', '1')]
```

# Second search: twisted shift s_g = x_1^-1 a x_1 (Attempt 1 on the node)

Group `<tau, w, s_g>` inside `B = V_2(<a>)`, with pieces `p -> (q, c)` meaning
`p u -> q a^c(u)` and exact reduced forms. Same limits: MSI, single core, 5 runs of at most
160 s each, nothing left running. The planted element `s_g tau s_g^-1 w` was recovered
(`StsW`, length 4). The tree test `is_aut` compares pairwise `T_3` distances of pieces. It
was calibrated: `tau`, `w`, `x_0` and `v_10` pass, `x_1` fails.

## Script (vbsearch.py)
```python
# BFS in the odometer Nekrashevych group B = V_2(<a>) on binary sequences (lowest digit first).
# Element = dict p -> (q, c): p u |-> q a^c(u), a = odometer (+1 with carry). Exact, reduced (maximal pieces).
import sys, time
def val(r): return sum(int(b) << i for i, b in enumerate(r))
def word(v, k): return ''.join(str((v >> i) & 1) for i in range(k))
def norm(g):
    g = dict(g); ch = True
    while ch:
        ch = False
        for p in list(g):
            if p and p[-1] == '0' and p in g and (p[:-1] + '1') in g:
                (r0, c0), (r1, c1) = g[p], g[p[:-1] + '1']
                if r0 and r1 and r0[:-1] == r1[:-1]:
                    q = r0[:-1]; c = None
                    if r0[-1] == '0' and r1[-1] == '1' and c0 == c1: c = 2 * c0
                    elif r0[-1] == '1' and r1[-1] == '0' and c1 == c0 + 1: c = 2 * c0 + 1
                    if c is not None:
                        del g[p]; del g[p[:-1] + '1']; g[p[:-1]] = (q, c); ch = True; break
    return frozenset(g.items())
def compose(g, h):  # g o h
    G = dict(g); out = {}; st = [(p, q, c) for p, (q, c) in h]
    while st:
        p, q, c = st.pop(); hit = None
        for pp in G:
            if q.startswith(pp): hit = pp; break
        if hit is not None:
            gq, gc = G[hit]; r = q[len(hit):]; k = len(r); t = val(r) + gc
            out[p] = (gq + word(t % (1 << k), k), (t >> k) + c)
        else:
            for b in (0, 1):
                t = b + c; st.append((p + str(b), q + str(t % 2), t >> 1))
    return norm(out)
def inv(g):  # p u -> q a^c(u)  inverse: q v -> p a^-c(v)
    return norm({q: (p, -c) for p, (q, c) in g})
def V(d): return norm({p: (q, 0) for p, q in d.items()})
ID = V({'': ''}); a = norm({'': ('', 1)})
tau = V({'0': '1', '1': '0'}); w = V({'1': '01', '01': '00', '00': '1'})
x0 = V({'0': '00', '10': '01', '11': '1'}); x1 = V({'0': '0', '10': '100', '110': '101', '111': '11'})
def swap(z):
    d = {z + '0': z + '1', z + '1': z + '0'}
    for i in range(len(z)): d[z[:i] + ('1' if z[i] == '0' else '0')] = z[:i] + ('1' if z[i] == '0' else '0')
    return V(d)
twists = {'x1': x1, 'x1inv': inv(x1), 't00_10': V({'00': '10', '10': '00', '01': '01', '11': '11'})}
tw = sys.argv[1]; maxlen = int(sys.argv[2]); cap = int(sys.argv[3])
g = twists[tw]; sg = compose(inv(g), compose(a, g))
assert compose(tau, w) == inv(x0), 'sanity: tau w = x0^-1'
gens = {'t': tau, 'W': w, 'w': inv(w), 'S': sg, 's': inv(sg)}
targets = {'x1': x1, 'v0': swap('0'), 'v1': swap('1'), 'v10': swap('10'), 'a_itself': a}
cal = compose(sg, compose(tau, compose(inv(sg), w)))  # planted, length 4
targets['CAL'] = cal
tset = {v: k for k, v in targets.items()}
print('twist', tw, 'sg pieces', len(sg), sorted(sg)[:6], flush=True)
t0 = time.time(); seen = {ID: ''}; fr = [ID]; found = {}
for L in range(1, maxlen + 1):
    nx = []
    for e in fr:
        we = seen[e]
        for n, s in gens.items():
            h = compose(s, e)
            if h not in seen:
                seen[h] = n + we; nx.append(h)
                if h in tset and tset[h] not in found:
                    found[tset[h]] = (L, seen[h]); print('FOUND', tset[h], L, seen[h], flush=True)
        if len(seen) > cap or time.time() - t0 > 250: break
    fr = nx
    print('len', L, 'total', len(seen), round(time.time() - t0, 1), flush=True)
    if len(seen) > cap or time.time() - t0 > 250: print('STOP budget'); break
print('DONE', tw, found)
```

## Added analysis (vtree.py, vcyc.py, vboot.py tails)
```python
def dist(x, y):
    if x[0] != y[0]: return len(x) + len(y) - 1
    k = 0
    while k < min(len(x), len(y)) and x[k] == y[k]: k += 1
    return len(x) + len(y) - 2 * k
def is_aut(e):
    ps = sorted(e)
    if any(c != 0 for p, (q, c) in ps): return None
    if len(ps) == 1: return ps[0][0] == ps[0][1][0]
    if any(p == '' or q == '' for p, (q, c) in ps): return False
    return all(dist(p1, p2) == dist(q1, q2) for (p1, (q1, _)) in ps for (p2, (q2, _)) in ps if p1 < p2)
L1 = int(sys.argv[4]); t0 = time.time(); seen = {ID: ''}; fr = [ID]
for L in range(1, L1 + 1):
    nx = []
    for e in fr:
        for n, s in gens.items():
            h = compose(s, e)
            if h not in seen: seen[h] = n + seen[e]; nx.append(h)
    fr = nx
gi = inv(g); stats = {}
for e in seen:
    if not all(c == 0 for p, (q, c) in e): continue
    k = (is_aut(e), is_aut(compose(g, compose(e, gi))), is_aut(compose(gi, compose(e, g))))
    stats[k] = stats.get(k, 0) + 1
print('L', L1, 'total', len(seen), 'pureV stats (autT3, aut g-conj, aut g^-1-conj):', stats)
# is s_g itself a T3 automorphism? and which tree does it preserve
print('s_g aut T3', is_aut(sg) , 'g s_g g^-1 = a?', compose(g, compose(sg, gi)) == a)
def in_T(e):  # pure V element: images of lex-ordered pieces form a cyclic rotation of the lex order of images
    ps = sorted(e); imgs = [q for p, (q, c) in ps]
    srt = sorted(imgs); k = srt.index(imgs[0])
    return imgs == srt[k:] + srt[:k]
def in_F(e):
    ps = sorted(e); imgs = [q for p, (q, c) in ps]; return imgs == sorted(imgs)
st = {}
for e in seen:
    if not all(c == 0 for p, (q, c) in e): continue
    k = (in_T(e), in_F(e)); st[k] = st.get(k, 0) + 1
print('L', L1, 'pureV (inT, inF):', st)
print('calib inT', [(n, in_T(t)) for n, t in [('tau', tau), ('w', w), ('x0', x0), ('x1', x1), ('v10', swap('10'))]])
L1 = int(sys.argv[4]) if len(sys.argv) > 4 else 8; K = int(sys.argv[5]) if len(sys.argv) > 5 else 60
t0 = time.time(); seen = {ID: ''}; fr = [ID]
for L in range(1, L1 + 1):
    nx = []
    for e in fr:
        for n, s in gens.items():
            h = compose(s, e)
            if h not in seen: seen[h] = n + seen[e]; nx.append(h)
    fr = nx
pv = [e for e in seen if e != ID and all(c == 0 for p, (q, c) in e)]
pv.sort(key=lambda e: (len(e), len(seen[e])))
G2 = pv[:K]
print('phase1', len(seen), 'pureV', len(pv), 'using', len(G2), round(time.time() - t0, 1), flush=True)
seen2 = {ID: ''}; fr = [ID]; found = {}
for L in range(1, 4):
    nx = []
    for e in fr:
        for gg in G2:
            h = compose(gg, e)
            if h not in seen2:
                seen2[h] = seen[gg] + seen2[e]; nx.append(h)
                if h in tset and tset[h] not in found:
                    wd = seen2[h]; ok = evalw(wd) == h
                    found[tset[h]] = (len(wd), wd, ok); print('FOUND', tset[h], len(wd), 'verified', ok, wd, flush=True)
        if len(seen2) > cap or time.time() - t0 > 250: break
    fr = nx
    print('phase2 depth', L, 'total', len(seen2), round(time.time() - t0, 1), flush=True)
    if len(seen2) > cap or time.time() - t0 > 250: print('STOP budget'); break
print('DONE', tw, {k: v[:1] + v[2:] for k, v in found.items()})
```

## Outputs
```
== tw_x1
twist x1 sg pieces 6 [('000', ('10', 0)), ('001', ('110', 0)), ('01', ('111', 0)), ('10', ('010', 0)), ('110', ('011', 0)), ('111', ('00', 1))]
len 1 total 6 0.0
len 2 total 24 0.0
len 3 total 90 0.0
FOUND CAL 4 StsW
len 4 total 330 0.0
len 5 total 1206 0.1
len 6 total 4398 0.3
len 7 total 16038 1.3
len 8 total 58470 3.9
len 9 total 213174 12.8
len 10 total 777144 48.0
len 11 total 2500002 157.9
STOP budget
DONE x1 {'CAL': (4, 'StsW')}
== scan_x1
twist x1 sg pieces 6 [('000', ('10', 0)), ('001', ('110', 0)), ('01', ('111', 0)), ('10', ('010', 0)), ('110', ('011', 0)), ('111', ('00', 1))]
len 1 total 6 0.0
len 2 total 24 0.0
len 3 total 90 0.0
FOUND CAL 4 StsW
len 4 total 330 0.0
len 5 total 1206 0.1
len 6 total 4398 0.2
len 7 total 16038 1.0
len 8 total 58470 3.6
len 9 total 213174 12.5
DONE x1 {'CAL': (4, 'StsW')}
pureV 3482 non-T3-automorphisms 3328
NONAUT 7 [('000', '00'), ('001', '011'), ('010', '111'), ('011', '010'), ('10', '100'), ('110', '101'), ('111', '110')] Swts
NONAUT 7 [('00', '000'), ('010', '011'), ('011', '001'), ('100', '10'), ('101', '110'), ('110', '111'), ('111', '010')] StWs
NONAUT 7 [('00', '100'), ('010', '101'), ('011', '110'), ('100', '00'), ('101', '011'), ('110', '111'), ('111', '010')] Swtst
NONAUT 7 [('000', '10'), ('001', '110'), ('010', '111'), ('011', '010'), ('10', '000'), ('110', '011'), ('111', '001')] StWst
NONAUT 7 [('000', '100'), ('0010', '101'), ('0011', '110'), ('010', '00'), ('011', '011'), ('10', '111'), ('11', '010')] SwtsW
NONAUT 7 [('0000', '10'), ('0001', '110'), ('0010', '111'), ('0011', '010'), ('01', '000'), ('10', '011'), ('11', '001')] StWsW
NONAUT 7 [('000', '111'), ('001', '010'), ('010', '100'), ('0110', '101'), ('0111', '110'), ('10', '00'), ('11', '011')] Swtsw
NONAUT 7 [('000', '011'), ('001', '001'), ('0100', '10'), ('0101', '110'), ('0110', '111'), ('0111', '010'), ('1', '000')] StWsw
calib is_aut [('tau', True), ('w', True), ('x0', True), ('x1', False), ('v10', True)]
== boot_x1
phase1 58470 pureV 1305 using 80 3.9
phase2 depth 1 total 81 3.9
phase2 depth 2 total 1107 4.1
phase2 depth 3 total 14049 7.7
DONE x1 {}
== tree_x1
L 8 total 58470 pureV stats (autT3, aut g-conj, aut g^-1-conj): {(True, True, True): 1, (True, False, False): 103, (False, False, False): 1200, (True, False, True): 1, (True, True, False): 1}
s_g aut T3 None g s_g g^-1 = a? True
== cyc_x1
L 9 pureV (inT, inF): {(True, True): 9, (True, False): 145, (False, False): 3328}
calib inT [('tau', True), ('w', True), ('x0', True), ('x1', True), ('v10', False)]
```
