# Irreducibility certificate through an invariant subtree and a self-replicating stabilizer.
# Setting: H_x = pr_V(<A>) acting on the vertical tree T_V (reduced vertical words; side H swaps the roles).
# (1) If some vertical letter f is fixed by every generator (hence, sections being generators, by every
#     element of H_x at every position), then the set of reduced words l0 f l1 f l2 ... (l_j != f) and their
#     prefixes is an H_x-invariant subtree; it is a copy of the full rooted tree X = (letters != f)^* and the
#     restricted action is that of the automaton group K with states = generators, output a.l = step(a,l)[0]
#     and section a|_l = (a|_l)|_f.  K is a quotient of H_x, so K infinite => H_x infinite.
#     (This needs f to be an involution letter so that l f l' is reduced for all l, l' != f.)
# (2) K is infinite if for some vertex v of X with |K.v| > 1 the section map Stab_K(v) -> K, k -> k|_v (a
#     homomorphism) is onto: a finite group has no proper subgroup mapping onto it.  Ontoness is certified by
#     writing every generator of K as a product of sections of Schreier generators of Stab_K(v); each identity
#     is checked exactly (w trivial in K iff every reachable state acts trivially on letters; finite search).
# Then H_x is infinite, pr_V(Gamma) is non-discrete and Gamma is irreducible (Burger-Mozes, Prop. 1.2).
# usage: selfrep.py census.json side depth prodlen idx...
import sys, json, itertools
from lo_census import load
from irred import letter_maps

def build(G, side):
    nL, inp, step, invL = letter_maps(G, side == 'H')
    invT = G.iA if side == 'H' else G.iB
    fixed = [f for f in range(inp) if invT[f] == f and all(step(a, f)[0] == f for a in range(nL))]
    if not fixed: return None
    f = fixed[0]; X = [l for l in range(inp) if l != f]
    out = {(a, l): step(a, l)[0] for a in range(nL) for l in X}
    sec = {(a, l): step(step(a, l)[1], f)[1] for a in range(nL) for l in X}
    return dict(f=f, X=X, nL=nL, invL=invL, out=out, sec=sec)

def act(K, w, l):
    s = list(w)
    for j in range(len(w) - 1, -1, -1):
        l2 = K['out'][(s[j], l)]; s[j] = K['sec'][(s[j], l)]; l = l2
    return l, tuple(s)

def act_path(K, w, v):
    y = []
    for l in v:
        l, w = act(K, w, l); y.append(l)
    return tuple(y), w

def trivial(K, w):
    seen = {w}; todo = [w]
    while todo:
        u = todo.pop()
        for l in K['X']:
            y, u2 = act(K, u, l)
            if y != l: return False
            if u2 not in seen:
                seen.add(u2); todo.append(u2)
                if len(seen) > 3_000_000: return None
    return True

def inv(K, w): return tuple(K['invL'][a] for a in reversed(w))

def certify(K, depth, plen):
    gens = [(a,) for a in range(K['nL'])]
    for d in range(1, depth + 1):
        for v in itertools.product(K['X'], repeat=d):
            # orbit and transversal of v at level d
            rep = {v: ()}; todo = [v]
            while todo:
                u = todo.pop()
                for g in gens:
                    u2, _ = act_path(K, g, u)
                    if u2 not in rep: rep[u2] = g + rep[u]; todo.append(u2)
            if len(rep) == 1: continue
            sch = set()
            for u, r in rep.items():
                for g in gens:
                    u2, _ = act_path(K, g + r, v)
                    w = inv(K, rep[u2]) + g + r
                    y, s = act_path(K, w, v); assert y == v
                    sch.add(s)
            secs = sorted(sch, key=len)
            pool = sorted({s for s in secs + [inv(K, s) for s in secs] if s}, key=lambda s: (len(s), s))
            found = {}
            for a in range(K['nL']):
                for k in range(1, plen + 1):
                    for combo in itertools.product(pool, repeat=k):
                        w = sum(combo, ()) + inv(K, (a,))
                        if trivial(K, w):
                            found[a] = combo; break
                    if a in found: break
                if a not in found: break
            if len(found) == K['nL']:
                return dict(v=v, orbit=len(rep), expressions={str(a): [list(c) for c in found[a]] for a in found})
    return None

if __name__ == "__main__":
    path, side, depth, plen = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    want = set(map(int, sys.argv[5:]))
    for i, G in load(path):
        if i in want:
            K = build(G, side)
            r = None if K is None else certify(K, depth, plen)
            print(json.dumps(dict(census=path, idx=i, side=side, fixed_letter=None if K is None else K['f'],
                                  depth=depth, prodlen=plen, certificate=r)), flush=True)
