# Exhaustive composition search for the length-six KL torsion residue.
# Looks for identities w ~ sigma_u(v) in A * <t> (up to cyclic conjugacy, w or w^-1),
# v in A * <z> of z-length k, u in A * <t> of t-length m, both nonsingular, k, m >= 2.
# If found, kl-substituting-a-short-inner-word-preserves-injectivity settles the word
# over every quotient of A, i.e. over every group with involution loops (case INV) or
# with y = g x g^-1 (case REL).
# Usage: python3 compsearch.py CASE K M L   (L = max coefficient word length)
import sys, itertools
CASE, K, M, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
# letters: 1=t,-1=T, 2=g,-2=G, 3=x (involution), 4=y (involution, INV only), 9=z,-9=Z
T, G, X, Y, Z = 1, 2, 3, 4, 9
INVOL = {X, Y}
def inv_letter(a): return a if a in INVOL else -a
def red(w):
    s = []
    for a in w:
        if s and s[-1] == inv_letter(a): s.pop()
        else: s.append(a)
    return s
def inv(w): return [inv_letter(a) for a in reversed(w)]
def cyc(w):
    w = red(w)
    while len(w) > 1 and w[0] == inv_letter(w[-1]): w = w[1:-1]
    return w
def canon(w):
    w = cyc(w); n = len(w)
    if n == 0: return ()
    return min(tuple(w[i:] + w[:i]) for i in range(n))
def tlen(w): return sum(1 for a in w if abs(a) == T)
def deg(w, v): return sum(1 if a == v else (-1 if a == -v else 0) for a in w)
# coefficient elements of A up to length L
gens = [G, -G, X] + ([Y] if CASE == "INV" else [])
coef = {()}
frontier = [()]
for _ in range(L):
    nf = []
    for c in frontier:
        for a in gens:
            d = tuple(red(list(c) + [a]))
            if len(d) == len(c) + 1 and d not in coef:
                coef.add(d); nf.append(d)
    frontier = nf
coef = sorted(coef, key=lambda c: (len(c), c))
Yw = [Y] if CASE == "INV" else [G, X, -G]   # REL: y = g x g^-1
def word(P, N, loopy=True):
    # +++++- : t a1 t a2 t a3 t a4 t y T x ; ++++-- : t a1 t a2 t a3 t y T 1 T x
    if len(P) == 4:
        w = [T]
        for a in P: w += a + [T]
        return w + Yw + [-T, X]
    w = [T]
    for a in P: w += a + [T]
    return w + Yw + [-T, -T, X]
gg = [G]; one = []
targets = {}
if CASE == "INV":
    for nm, P in [("1111", (one,one,one,one)), ("111g", (one,one,one,gg)), ("11g1", (one,one,gg,one)),
                  ("1g11", (one,gg,one,one)), ("g111", (gg,one,one,one)),
                  ("11gg", (one,one,gg,gg)), ("1g1g", (one,gg,one,gg)), ("1gg1", (one,gg,gg,one)),
                  ("--11g", (one,one,gg)), ("--g11", (gg,one,one)), ("--1gg", (one,gg,gg)),
                  ("--gg1", (gg,gg,one)), ("--g1g", (gg,one,gg)), ("--ggg", (gg,gg,gg)),
                  ("--111ctrl", (one,one,one)), ("--1g1ctrl", (one,gg,one))]:
        w = word(P, None)
        targets[canon(w)] = nm; targets[canon(inv(w))] = nm + "^-1"
else:
    for nm, P in [("R111g", (one,one,one,gg)), ("R11g1", (one,one,gg,one)),
                  ("R1g11", (one,gg,one,one)), ("Rg111", (gg,one,one,one))]:
        w = word(P, None)
        targets[canon(w)] = nm; targets[canon(inv(w))] = nm + "^-1"
tdeg = {}
for c, nm in targets.items(): tdeg[nm] = abs(deg(list(c), T))
def patterns(n, want):
    for e in itertools.product((1, -1), repeat=n):
        if abs(sum(e)) in want: yield e
def words(n, letter, want, coefs, lead):
    # letter^{e1} c1 letter^{e2} ... ; lead=False: no trailing coefficient (inner u), True: trailing d_k (outer v)
    for e in patterns(n, want):
        for cs in itertools.product(coefs, repeat=(n if lead else n - 1)):
            w = []
            ok = True
            for i in range(n):
                if i > 0:
                    c = cs[i - 1]
                    if not c and e[i] == -e[i - 1]: ok = False; break
                    w += list(c)
                w.append(letter * e[i])
            if not ok: continue
            if lead:
                c = cs[n - 1]
                if not c and e[0] == -e[-1]: continue
                w += list(c)
            yield w
degs = sorted(set(tdeg.values()))
found = 0; tested = 0
for dv in range(1, K + 1):
    for du in range(1, M + 1):
        if dv * du not in degs: continue
        us = list(words(M, T, {du}, coef, False))
        for v in words(K, Z, {dv}, coef, True):
            for u in us:
                img = []
                ui = inv(u)
                for a in v:
                    if a == Z: img += u
                    elif a == -Z: img += ui
                    else: img.append(a)
                tested += 1
                if tlen(red(img)) > 12: pass
                cw = canon(img)
                if len(cw) and cw in targets:
                    nm = targets[cw]
                    if tdeg[nm] == dv * du:
                        found += 1
                        print("FOUND", nm, "v=", v, "u=", u, flush=True)
print("CASE", CASE, "K", K, "M", M, "L", L, "tested", tested, "found", found)
print("DONE")
