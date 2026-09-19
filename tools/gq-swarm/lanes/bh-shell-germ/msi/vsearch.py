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
