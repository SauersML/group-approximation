#!/usr/bin/env python3
"""Integral census of M_L from the R-chains of twisted.py (restriction of
scalars R = Z[t]/(t^3-1) -> Z^3), through sylow.lattice_from_rs.

Q = Z^{3 ngen}/rows is H_1(M_L) + Z^2 (twisted.py), so the printed H_1 has
two extra free summands; the twist classes, W and d are those of M_L.
Used as a test: base U with L = max<k> must reproduce pbar.py's census of
Gamma_{max_k} (H_1 = Z^18 + (Z/3)^10 for max0, Z^28 + (Z/3)^4 for max1).

Usage: python3 zform.py U max0 [out.json]
"""
import json
import sys

import twisted as T
import sylow as S
import fastelim


def shift(v, e):
    """t^e * v for an R-row v (dict gen -> [a0, a1, a2])."""
    return {g: [a[(k - e) % 3] for k in range(3)] for g, a in v.items()}


def zrows(v):
    out = {}
    for g, a in v.items():
        for k in range(3):
            if a[k]:
                out[3 * g + k] = a[k]
    return out


def main(base, which, outp=None):
    ngen, R, Z, zinfo, info = T.build(which, base=base)
    rows = [zrows(shift(r, e)) for r in R for e in range(3)]
    vs = [zrows(shift(z, e)) for z in Z for e in range(3)]
    out, _ = S.lattice_from_rs(3 * ngen, rows, vs, f"zform-{base}-{which}",
                               3 * info["base_cosets"],
                               elim=fastelim.eliminate)
    out.update(info)
    if outp:
        json.dump(out, open(outp, "w"), indent=1)


if __name__ == "__main__":
    main(*sys.argv[1:])
