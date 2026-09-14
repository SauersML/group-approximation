# Second planted control, in PSL(2,17) acting on the projective line (right action, as in
# gen_ctrl.py). It finds a, b, c with <a,b> = S4 (a^2 = b^3 = (ab)^4 = 1), <a,c> = S3
# (c^2 = (ac)^3 = 1), <a,b> and <a,c> meeting in <a>, and <a,b,c> = PSL(2,17), of order 2448.
# Then it writes four reduced words over a, b, b^-1, c, with the lengths of r5..r8, that are
# trivial in the group.
# Why this control: a subgroup H of G gives an exact free gluing on H\G exactly when H meets every
# conjugate of <a,b> and <a,c> trivially. In PSL(2,17) all involutions are conjugate, and so are
# all subgroups of order 3, and <a,b> contains both kinds. So H must have order prime to 6, i.e.
# H = 1 or a subgroup of order 17. The exact gluings coming from G have 144 or 2448 points per
# component, so no 24-point components exist through this quotient.
import random, sys
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
random.seed(seed)
p = 17; INF = p; N = p + 1
def mob(m, x):
    a, b, c, d = m
    if x == INF:
        return INF if c == 0 else (a * pow(c, -1, p)) % p
    den = (c * x + d) % p
    if den == 0: return INF
    return ((a * x + b) * pow(den, -1, p)) % p
def perm(m): return tuple(mob(m, x) for x in range(N))
def mul(s, t): return tuple(t[s[i]] for i in range(N))       # first s then t
E = tuple(range(N))
def inv(s):
    r = [0]*N
    for i in range(N): r[s[i]] = i
    return tuple(r)
def closure(gens):
    S = {E}; fr = [E]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = mul(x, g)
                if y not in S: S.add(y); nf.append(y)
        fr = nf
    return S
def order(s):
    x, n = s, 1
    while x != E: x = mul(x, s); n += 1
    return n
G = closure([perm((1, 1, 0, 1)), perm((0, 16, 1, 0)), perm((3, 0, 0, 6))])
assert len(G) == 2448, len(G)
Gl = list(G)
inv2 = [g for g in Gl if order(g) == 2]; ord3 = [g for g in Gl if order(g) == 3]
while True:
    a = random.choice(inv2); b = random.choice(ord3)
    if order(mul(a, b)) != 4: continue
    S4 = closure([a, b])
    if len(S4) != 24: continue
    cs = [c for c in inv2 if order(mul(a, c)) == 3]
    random.shuffle(cs)
    ok = None
    for c in cs:
        S3 = closure([a, c])
        if len(S3) == 6 and S4 & S3 == {E, a} and len(closure([a, b, c])) == 2448:
            ok = c; break
    if ok is not None: c = ok; break
LET = {'a': a, 'b': b, 'B': inv(b), 'c': c}
INVL = {'a': 'a', 'c': 'c', 'b': 'B', 'B': 'b'}
BAD = {'aa', 'cc', 'bB', 'Bb', 'bb', 'BB'}
def val(w):
    x = E
    for ch in w: x = mul(x, LET[ch])
    return x
def rw(L):
    w = [random.choice('abBc')]
    while len(w) < L:
        ch = random.choice('abBc')
        if w[-1] + ch not in BAD: w.append(ch)
    return w
def fmt(w): return ''.join('b^-1' if ch == 'B' else ch for ch in w)
print("a =", a); print("b =", b); print("c =", c)
print("|<a,b>| =", len(closure([a, b])), "|<a,c>| =", len(closure([a, c])), "|<a,b,c>| =", len(closure([a, b, c])))
print("all involutions conjugate:", len({min(mul(mul(inv(g), x), g) for g in Gl) for x in inv2}) == 1)
print("all elements of order 3 conjugate:", len({min(mul(mul(inv(g), x), g) for g in Gl) for x in ord3}) == 1)
print("orders present:", sorted({order(g) for g in Gl}))
lens = [26, 28, 26, 37]
ctrl = []
for L in lens:
    while True:
        u = rw((L + 1) // 2); target = val(u); found = None
        for _ in range(200000):
            w = rw(L // 2)
            if val(w) == target: found = w; break
        if found is None: continue
        rel = u + [INVL[ch] for ch in reversed(found)]
        if any(rel[t] + rel[t+1] in BAD for t in range(len(rel) - 1)) or rel[-1] + rel[0] in BAD: continue
        assert val(rel) == E and len(rel) == L
        ctrl.append(fmt(rel)); break
with open('rel_CTRL2.txt', 'w') as f:
    for r in ctrl: f.write(r + '\n')
for r in ctrl: print("CTRL2:", r)
print("GENDONE")
