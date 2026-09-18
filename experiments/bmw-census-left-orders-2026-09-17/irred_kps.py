# Irreducibility certificate by an infinite-order element of H_x = pr_V(<A>) (vertex stabilizer of the
# projection of Gamma to the vertical tree).  For a horizontal word g and a vertical word u with g-orbit of
# length k > 1, the section s = g^k|_u (a horizontal word, computed exactly with SQ) satisfies
# pr_V(s) = pr_V(u^-1 g^k u).  If pr_V(s) = pr_V(c g^e c^-1) for some horizontal c and e = +-1, then pr_V(g)
# has infinite order: were its order N finite, k | N (orbit length) and ord(g^k) = ord(g) forces gcd(k, N) = 1.
# Equality in H_x is decided exactly: pr_V(w) = 1 iff every reachable (state, last letter) acts trivially on
# the next letter (kernel.trivial; the states are words of fixed length, so the search is finite).
# Then H_x is infinite, pr_V(Gamma) is non-discrete and Gamma is irreducible (Burger-Mozes, Prop. 1.2).
# usage: irred_kps.py census.json side Lg Lu Lc idx...      side V: <A> on T_V; side H: <B> on T_H
import sys, json, itertools
from lo_census import load
from irred_tw import maps
from kernel import trivial

def red(w, inv):
    out = []
    for x in w:
        if out and inv[out[-1]] == x: out.pop()
        else: out.append(x)
    return tuple(out)

def reduced_words(n, inv, L):
    for k in range(1, L + 1):
        for w in itertools.product(range(n), repeat=k):
            if all(inv[w[i]] != w[i + 1] for i in range(k - 1)): yield w

def act_word(step, g, u):
    # image of the vertical word u under the horizontal word g (g acts letter by letter, rightmost first:
    # g = g_1...g_l acts as g_1 o ... o g_l), and the section g|_u
    st = list(g); y = []
    for x in u:
        for j in range(len(st) - 1, -1, -1):
            x, st[j] = step(st[j], x)
        y.append(x)
    return tuple(y), tuple(st)

def search(G, side, Lg, Lu, Lc):
    L, n, invT, step = maps(G, side)
    invL = G.iA if side == 'V' else G.iB
    stepp = lambda a, x: step(a, x)
    for g in reduced_words(L, invL, Lg):
        ginv = tuple(invL[x] for x in reversed(g))
        for u in reduced_words(n, invT, Lu):
            k, v, s = 1, u, ()
            v, s1 = act_word(stepp, g, u)
            while v != u and k < 64:
                v, _ = act_word(stepp, g, v); k += 1
            if v != u or k == 1: continue
            gk = g * k
            v, s = act_word(stepp, gk, u); assert v == u
            s = red(s, invL)
            for c in itertools.chain([()], reduced_words(L, invL, Lc)):
                cinv = tuple(invL[x] for x in reversed(c))
                for e, ge in ((1, ginv), (-1, g)):     # test s * (c g^e c^-1)^-1 = s c g^-e c^-1
                    w = red(s + c + ge + cinv, invL)
                    if not w: return dict(g=g, u=u, k=k, c=c, e=e, section=s)
                    t = trivial(step, n, invT, w)
                    if t: return dict(g=g, u=u, k=k, c=c, e=e, section=s)
    return None

if __name__ == "__main__":
    path, side, Lg, Lu, Lc = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    want = set(map(int, sys.argv[6:]))
    for i, G in load(path):
        if i in want:
            r = search(G, side, Lg, Lu, Lc)
            print(json.dumps(dict(census=path, idx=i, side=side, Lg=Lg, Lu=Lu, Lc=Lc, certificate=r)), flush=True)
