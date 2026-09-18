"""Independent check of Theorem A's hypothesis: search short products w of the
generators of H_s = <s, v> with g^-1 w g also in H_s for g = t^{+-1}, by
Stallings-graph membership. A hit is an explicit nontrivial element of
H_s cap g^-1 H_s g. No hit is expected for the no-contact words cdcDcd, ccdcDD.
Run from this directory: python3 witnesses.py"""
import itertools
from stallings import fold, read, inv, INV

def red(w):
    st = []
    for l in w:
        if st and st[-1] == INV[l]:
            st.pop()
        else:
            st.append(l)
    return ''.join(st)

def member(G, b, w):
    return read(G, b, w) == b

for v in ['cccddd', 'cdcdcD', 'ccdcdcd', 'cdcdcDD', 'cddcddcD', 'cdcDcd', 'ccdcDD']:
    found = None
    for s, t in (('c', 'd'), ('d', 'c')):
        gens = [s, v]
        G, b = fold(gens)
        alph = [s, INV[s], v, inv(v)]
        for n in range(1, 6):
            for tup in itertools.product(range(4), repeat=n):
                w = red(''.join(alph[i] for i in tup))
                if not w:
                    continue
                for g in (t, INV[t]):
                    cw = red(INV[g] + w + g)
                    if member(G, b, cw):
                        found = (s, g, w, cw)
                        break
                if found: break
            if found: break
        if found: break
    print(v, found)
