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
