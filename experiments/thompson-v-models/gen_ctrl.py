# Planted control for vglue.c. Under a = (0 1), b = (1 2 3), c = (0 4) in S5 (right action),
# <a,b> = S4, <a,c> = S3, and they meet in <a>; so S5 is a quotient of S4 *_{C2} S3, and a
# free S5-set of size 120m is an exact free gluing. This writes four reduced words over
# a, b, b^-1, c with the lengths of the long relators of (2.4) that are trivial in S5. It also
# reports the S5 values of the four long relators of V, which are not planted.
import random, sys
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
random.seed(seed)
def mul(p, q):  # first p then q
    return tuple(q[p[i]] for i in range(5))
A = (1, 0, 2, 3, 4); B = (0, 2, 3, 1, 4); C = (4, 1, 2, 3, 0)
Bi = [0]*5
for i in range(5): Bi[B[i]] = i
Bi = tuple(Bi); E = (0, 1, 2, 3, 4)
LET = {'a': A, 'b': B, 'B': Bi, 'c': C}
INV = {'a': 'a', 'c': 'c', 'b': 'B', 'B': 'b'}
BAD = {'aa', 'cc', 'bB', 'Bb', 'bb', 'BB'}
def val(w):
    p = E
    for x in w: p = mul(p, LET[x])
    return p
def expand(s):  # V relator syntax -> letters a, b, B, c
    out, i = [], 0
    def seq():
        nonlocal i
        res = []
        while i < len(s) and s[i] != ')':
            if s[i] == '(':
                i += 1; body = seq(); i += 1
            else:
                body = [s[i]]; i += 1
            inv, rep = False, 1
            if i < len(s) and s[i] == '^':
                i += 1
                if s[i] == '-': inv = True; i += 1
                j = i
                while i < len(s) and s[i].isdigit(): i += 1
                rep = int(s[j:i])
            piece = [INV[x] for x in reversed(body)] if inv else body
            res += piece * rep
        return res
    return seq()
def rw(L):
    w = [random.choice('abBc')]
    while len(w) < L:
        x = random.choice('abBc')
        if w[-1] + x not in BAD: w.append(x)
    return w
def fmt(w):
    return ''.join('b^-1' if x == 'B' else x for x in w)
VREL = [l.strip() for l in open('rel_V.txt') if l.strip()]
lens = [len(expand(r)) for r in VREL]
print("V long relator lengths:", lens)
for r in VREL: print("S5 value of V relator:", val(expand(r)), "trivial:", val(expand(r)) == E)
print("|<a,b>|, |<a,c>|, |<a,b,c>| checks via closure")
def closure(gens):
    S = {E}; fr = [E]
    while fr:
        nf = []
        for p in fr:
            for g in gens:
                q = mul(p, g)
                if q not in S: S.add(q); nf.append(q)
        fr = nf
    return S
S4, S3, S5 = closure([A, B]), closure([A, C]), closure([A, B, C])
print(len(S4), len(S3), len(S5), "intersection:", len(S4 & S3))
ctrl = []
for L in lens:
    while True:
        u = rw((L + 1) // 2); target = val(u)
        found = None
        for _ in range(20000):
            w = rw(L // 2)
            if val(w) == target: found = w; break
        if found is None: continue
        rel = u + [INV[x] for x in reversed(found)]
        if any(rel[t] + rel[t+1] in BAD for t in range(len(rel) - 1)): continue
        if rel[-1] + rel[0] in BAD: continue
        assert val(rel) == E and len(rel) == L
        ctrl.append(fmt(rel)); break
with open('rel_CTRL.txt', 'w') as f:
    for r in ctrl: f.write(r + '\n')
for r in ctrl: print("CTRL:", r, "len", len(expand(r)), "trivial in S5:", val(expand(r)) == E)
print("GENDONE")
