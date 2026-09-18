# Infinite-order certificate inside the invariant-subtree group K (selfrep.build): for a word g of K and a
# vertex v of the ternary tree X^* whose g-orbit has length k > 1, s = g^k|_v.  If s = c g^e c^-1 in K
# (e = +-1, c a short word; equality checked exactly by selfrep.trivial) then g has infinite order in K:
# were ord(g) = N finite, k | N and ord(g^k|_v) <= ord(g^k) = N/k < N.  So K is infinite, hence H_x
# (which maps onto K) is infinite and Gamma is irreducible (Burger-Mozes, Prop. 1.2).
# usage: kkps.py census.json side Lg Lv Lc idx...
import sys, json, itertools
from lo_census import load
from selfrep import build, act_path, trivial, inv

def red(K, w):
    out = []
    for a in w:
        if out and K['invL'][out[-1]] == a: out.pop()
        else: out.append(a)
    return tuple(out)

def words(K, L):
    for k in range(1, L + 1):
        for w in itertools.product(range(K['nL']), repeat=k):
            if all(K['invL'][w[i]] != w[i + 1] for i in range(k - 1)): yield w

def search(K, Lg, Lv, Lc):
    for g in words(K, Lg):
        if trivial(K, g): continue
        for d in range(1, Lv + 1):
            for v in itertools.product(K['X'], repeat=d):
                u, k = act_path(K, g, v)[0], 1
                while u != v and k < 200: u = act_path(K, g, u)[0]; k += 1
                if u != v or k == 1: continue
                _, s = act_path(K, g * k, v); s = red(K, s)
                for c in itertools.chain([()], words(K, Lc)):
                    for ge in (inv(K, g), g):
                        w = red(K, s + c + ge + inv(K, c))
                        if not w or trivial(K, w):
                            return dict(g=g, v=v, k=k, c=c, e=1 if ge != g else -1, section=s)
    return None

if __name__ == "__main__":
    path, side, Lg, Lv, Lc = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    for i, G in load(path):
        if i in set(map(int, sys.argv[6:])):
            K = build(G, side)
            print(json.dumps(dict(census=path, idx=i, side=side, Lg=Lg, Lv=Lv, Lc=Lc, fixed_letter=K['f'],
                                  certificate=search(K, Lg, Lv, Lc))), flush=True)
