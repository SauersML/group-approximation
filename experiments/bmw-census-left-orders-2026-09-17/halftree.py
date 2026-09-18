# Irreducibility certificate by a half-tree fixator.  H = pr_V(Gamma) <= Aut(T_V), H_x = pr_V(<A>) the
# stabilizer of the base vertex x.  Look for a horizontal word h and a vertical letter y such that h acts
# trivially on the half-tree T_e = {x} u {vertical words not starting with y} (e = the edge from x to y) but
# nontrivially on T_V.  Then H_x is infinite: the vertical element g = y b (b != y) is hyperbolic on T_V with
# axis ..., b, x, y, yb, ... through e, translating from x towards y, so g^n h g^-n lies in H_x (it fixes
# g^n T_e, which contains x), is nontrivial, and fixes g^n T_e, which contains the ball B(x, 2n).  A finite
# group of tree automorphisms acts faithfully on some finite ball, so H_x is infinite, pr_V(Gamma) is
# non-discrete and Gamma is irreducible (Burger-Mozes, Lattices in product of trees, Prop. 1.2).
# Both tests are exact: a state is (current section word, last vertical letter read); the inputs at a state
# are the letters x != inv[last] (for the half-tree the first input avoids y, i.e. start with last = inv[y]).
# usage: halftree.py census.json L side idx...        side V: <A> on T_V; side H: <B> on T_H
import sys, json, itertools
from lo_census import load
from irred import letter_maps, act

def trivial_from(step, inp, inv, w, last):
    seen = {(w, last)}; todo = [(w, last)]
    while todo:
        u, lst = todo.pop()
        for x in range(inp):
            if lst is not None and x == inv[lst]: continue
            y, u2 = act(step, u, x)
            if y != x: return False
            if (u2, x) not in seen:
                seen.add((u2, x)); todo.append((u2, x))
                if len(seen) > 2_000_000: return None
    return True

def search(G, side, L):
    nL, inp, step, invL = letter_maps(G, side == 'H')
    invT = G.iA if side == 'H' else G.iB
    for k in range(1, L + 1):
        for w in itertools.product(range(nL), repeat=k):
            if any(invL[w[i]] == w[i + 1] for i in range(k - 1)): continue
            for y in range(inp):
                if trivial_from(step, inp, invT, w, invT[y]) and trivial_from(step, inp, invT, w, None) is False:
                    return dict(word=w, y=y)
    return None

if __name__ == "__main__":
    path, L, side = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    want = set(map(int, sys.argv[4:]))
    for i, G in load(path):
        if i in want:
            print(json.dumps(dict(census=path, idx=i, L=L, side=side, certificate=search(G, side, L))), flush=True)
