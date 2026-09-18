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
