#!/usr/bin/env python3
"""For each linear bouquet: the bounded subgroup B = <alpha, beta, t> (it contains T = l_t),
an exact contraction certificate for B (nucleus N_B), and the set L of z^p-loops of B inside N_B:
c in N_B fixing z^p with c|_{z^p} = c (Lemma C of the node: G is contracting iff
H_P = <S, L> is finite).  Output: |N_B|, |L|, and whether L = <T> (as sets of elements).
Run: nice -n 10 timeout 1200 python3 loops_B.py > loops_B.out
"""
from bouquets import bouquets
from loopgraph import Rec, ID, W
from nucleus import contraction_certificate

def z_loops(E, NB, z):
    """ids c in NB with c fixing z^p and c|_{z^p} = c for some p >= 1"""
    out = set()
    for c in NB:
        d, seen = c, []
        while d not in seen:
            if E.perm[d][z] != z: break
            seen.append(d); d = E.sections(d)[z]
        else:
            if d == c: out.add(c)
    return out

def B_data(R, I, cache={}):
    key = (R.states["t"][0], tuple(sorted(R.states["t"][1].items())), I["z"])
    if key in cache: return cache[key]
    RB = Rec("B", R.rooted, {"t": R.states["t"]})
    E, NB, Y = contraction_certificate(RB, ["a", "e", "t"])
    L = z_loops(E, NB, I["z"])
    T = E.ident(I["T"]); powers, p = set(), E.ident(())
    while p not in powers: powers.add(p); p = E.ident(E.words[p] + I["T"])
    res = dict(NB=len(NB), L=len(L), L_is_T=(L == powers), ordT=len(powers),
               Lwords=sorted(E.words[c] for c in L - powers)[:3])
    cache[key] = res; return res

if __name__ == "__main__":
    tally = {}
    for name, R, I in bouquets():
        d = B_data(R, I)
        k = (d["NB"], d["L"], d["L_is_T"], d["ordT"])
        tally.setdefault(k, []).append(name)
        print(name, "| z =", I["z"], "|", {x: d[x] for x in ("NB", "L", "L_is_T", "ordT")},
              "" if d["L_is_T"] else f"extra loops e.g. {d['Lwords']}", flush=True)
    print("\n|N_B|, |L|, L = <T>, ord T : count")
    for k, v in sorted(tally.items(), key=lambda kv: -len(kv[1])): print(" ", k, ":", len(v))
