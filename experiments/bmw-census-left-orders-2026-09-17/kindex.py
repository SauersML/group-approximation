# Index certificate for infiniteness of the invariant-subtree group K (selfrep.build).
# For a vertex v with |K.v| = m > 1 the section map phi: Stab_K(v) -> K, k -> k|_v, is a homomorphism (K is
# self-similar).  If K were finite, |phi(Stab_K(v))| <= |Stab_K(v)| = |K|/m, so [K : phi(Stab_K(v))] >= m.
# Hence K is infinite as soon as phi(Stab_K(v)) contains a subgroup U of index < m.  Targets U: K itself
# (index 1), and U = <a, t a t : a in S \\ {t}> for a generating set S and an involution t in S (index <= 2).
# Containment is certified by writing each generator of U as a product of at most P elements of the pool
# (sections of Schreier generators of Stab_K(v) and their inverses); each identity is checked exactly.
# Then H_x (which maps onto K) is infinite and Gamma is irreducible (Burger-Mozes, Prop. 1.2).
# usage: kindex.py census.json side depth P idx...
import sys, json, itertools
from lo_census import load
from selfrep import build, act_path, trivial, inv
from kkps import red

def sign(K, a, n):
    V = list(itertools.product(K['X'], repeat=n)); ix = {v: i for i, v in enumerate(V)}
    p = [ix[act_path(K, (a,), v)[0]] for v in V]; seen = [False] * len(p); s = 1
    for i in range(len(p)):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]: seen[j] = True; j = p[j]; L += 1
            s *= (-1) ** (L - 1)
    return s

def generating_subsets(K):
    # subsets S of the generators such that every other generator equals (exactly, in K) a product of at most
    # three elements of S, so that K = <S>
    gens = list(range(K['nL'])); out = []
    for r in range(1, len(gens) + 1):
        for S in itertools.combinations(gens, r):
            expr = {}
            for b in gens:
                if b in S: continue
                for k in (1, 2, 3):
                    for w in itertools.product(S, repeat=k):
                        if trivial(K, red(K, w + inv(K, (b,)))): expr[b] = w; break
                    if b in expr: break
                if b not in expr: break
            if len(expr) == len(gens) - len(S): out.append((S, expr))
    return out

def targets(K):
    # K itself (index 1) and, for a generating subset S and an involution t in S, U = <a, t a t : a in S, a != t>:
    # t normalizes U (t (t a t) t = a) and U <t> contains S, so [K : U] <= 2 (whether or not K -> Z/2 exists).
    T = [('K', 1, [(a,) for a in range(K['nL'])])]
    for S, expr in generating_subsets(K):
        for t in S:
            if K['invL'][t] != t: continue
            U = sorted({red(K, u) for a in S if a != t for u in ((a,), (t, a, t)) if red(K, u)})
            T.append((f'U(S={list(S)}, t={t}; other generators: {expr})', 2, U))
    return T

def certify(K, depth, P):
    gens = [(a,) for a in range(K['nL'])]; T = targets(K)
    for d in range(1, depth + 1):
        for v in itertools.product(K['X'], repeat=d):
            rep = {v: ()}; todo = [v]
            while todo:
                u = todo.pop()
                for g in gens:
                    u2, _ = act_path(K, g, u)
                    if u2 not in rep: rep[u2] = g + rep[u]; todo.append(u2)
            m = len(rep)
            if m == 1: continue
            secs = set()
            for u, r in rep.items():
                for g in gens:
                    u2, _ = act_path(K, g + r, v)
                    w = inv(K, rep[u2]) + g + r
                    y, s = act_path(K, w, v); assert y == v
                    s = red(K, s)
                    if s: secs.add(s)
            pool = sorted(secs | {inv(K, s) for s in secs}, key=lambda s: (len(s), s))
            for name, index, U in T:
                if index >= m: continue
                found = {}
                for u in U:
                    for k in range(1, P + 1):
                        for combo in itertools.product(pool, repeat=k):
                            if trivial(K, red(K, sum(combo, ()) + inv(K, u))):
                                found[str(u)] = [list(c) for c in combo]; break
                        if str(u) in found: break
                    if str(u) not in found: break
                if len(found) == len(U):
                    return dict(v=v, orbit=m, target=name, index=index, target_gens=[list(u) for u in U], expressions=found)
    return None

if __name__ == "__main__":
    path, side, depth, P = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    for i, G in load(path):
        if i in set(map(int, sys.argv[5:])):
            K = build(G, side)
            print(json.dumps(dict(census=path, idx=i, side=side, fixed_letter=K['f'], depth=depth, P=P,
                                  targets=[(t[0], t[1], len(t[2])) for t in targets(K)], certificate=certify(K, depth, P))), flush=True)
