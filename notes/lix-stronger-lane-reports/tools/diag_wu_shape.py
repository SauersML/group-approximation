#!/usr/bin/env python3
"""Print the weight-(ip+1) component of the universal Wu polynomial E_{i+1},
i.e. the general-p analogue of the F2 tree's diagonal relation
    Sq^{2i} gamma_{i+1} = sum_{j<=i} gamma_{i-j} gamma_{i+1+j}.
Checks: the only LINEAR term is e_{ip+1}, with coefficient 1."""
import sys
sys.path.insert(0, ".")
from lix_modp_uniform_check import phi_universal

def show(p, imax=4, R=None):
    for i in range(1, imax + 1):
        N = i * p + 1
        RR = R or (N + 2)
        if N > RR:
            continue
        Es = phi_universal(RR, p)
        E = Es[i + 1]
        comp = {}
        for exps, c in E.items():
            w = sum((j + 1) * a for j, a in enumerate(exps))
            if w != N:
                continue
            lam = tuple(sorted([j + 1 for j, a in enumerate(exps) for _ in range(a)], reverse=True))
            comp[lam] = c
        lin = {k: v for k, v in comp.items() if len(k) == 1}
        s = " + ".join(f"{v}*e_{'e_'.join(map(str,k)) if len(k)>1 else k[0]}"
                       if len(k) == 1 else f"{v}*" + "".join(f"e_{x}" for x in k)
                       for k, v in sorted(comp.items()))
        print(f"  p={p} i={i}  P^{i}(gamma_{i+1}) = {s}")
        assert lin == {(N,): 1}, ("linear part is not e_N with coefficient 1", p, i, lin)
    print(f"  p={p}: linear part is e_(ip+1) with coefficient 1 in every case above")

for p in (2, 3, 5, 7):
    show(p, imax=3 if p <= 3 else 2)
