# Index certificate for infiniteness of the invariant-subtree group K (selfrep.build), vertex-stabilizer form.
# v a vertex with |K.v| = m, phi: Stab_K(v) -> K, k -> k|_v (a homomorphism; K is self-similar).  If K were
# finite, [K : phi(Stab_K(v))] >= m (as |phi(Stab_K(v))| <= |K|/m).  If phi(Stab_K(v)) contains Stab_K(w) for
# a vertex w with |K.w| < m, then [K : phi(Stab_K(v))] <= |K.w| < m, so K is infinite; H_x (which maps onto K)
# is infinite and Gamma is irreducible (Burger-Mozes, Prop. 1.2).
# Containment: each Schreier generator of Stab_K(w) is written as a product of elements of the pool (sections at
# v of Schreier generators of Stab_K(v), and inverses).  Candidate products are found by meet-in-the-middle on
# the action on level NL; every identity used is then checked exactly (selfrep.trivial).
# usage: kstab.py census.json side dv dw D NL idx...
import sys, json, itertools
from lo_census import load
from selfrep import build, act_path, trivial, inv
from kkps import red

def schreier(K, v):
    gens = [(a,) for a in range(K['nL'])]
    rep = {v: ()}; todo = [v]
    while todo:
        u = todo.pop()
        for g in gens:
            u2, _ = act_path(K, g, u)
            if u2 not in rep: rep[u2] = g + rep[u]; todo.append(u2)
    S = set()
    for u, r in rep.items():
        for g in gens:
            u2, _ = act_path(K, g + r, v); w = red(K, inv(K, rep[u2]) + g + r)
            if w: S.add(w)
    return len(rep), sorted(S, key=lambda s: (len(s), s))

def run(K, dv, dw, D, NL):
    V = list(itertools.product(K['X'], repeat=NL)); ix = {x: i for i, x in enumerate(V)}
    perm = lambda w: tuple(ix[act_path(K, w, x)[0]] for x in V)
    mul = lambda p, q: tuple(p[i] for i in q)
    def pinv(p):
        r = [0] * len(p)
        for i, x in enumerate(p): r[x] = i
        return tuple(r)
    for v in itertools.product(K['X'], repeat=dv):
        m, sch = schreier(K, v)
        secs = {red(K, act_path(K, s, v)[1]) for s in sch}; secs.discard(())
        pool = sorted(secs | {inv(K, s) for s in secs}, key=lambda s: (len(s), s))
        ball = {perm(()): ()}; fr = [(perm(()), ())]; P = [(s, perm(s)) for s in pool]
        for _ in range(D):
            nf = []
            for p, w in fr:
                for s, q in P:
                    r = mul(p, q)
                    if r not in ball: ball[r] = w + s; nf.append((r, w + s))
            fr = nf
        for w in itertools.product(K['X'], repeat=dw):
            mw, schw = schreier(K, w)
            if mw >= m: continue
            expr = {}
            for t in schw:
                pt = perm(t); hit = None
                for x, wx in ball.items():
                    y = mul(pinv(x), pt)
                    if y in ball:
                        cand = red(K, wx + ball[y])
                        if trivial(K, red(K, cand + inv(K, t))): hit = cand; break
                if hit is None: break
                expr[str(t)] = hit
            if len(expr) == len(schw):
                return dict(v=v, orbit_v=m, w=w, orbit_w=mw, pool=pool, stab_w_gens=schw, expressions=expr)
    return None

if __name__ == "__main__":
    path, side, dv, dw, D, NL = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:7])
    for i, G in load(path):
        if i in set(map(int, sys.argv[7:])):
            K = build(G, side)
            print(json.dumps(dict(census=path, idx=i, side=side, fixed_letter=K['f'], dv=dv, dw=dw, D=D, NL=NL,
                                  certificate=run(K, dv, dw, D, NL))), flush=True)
