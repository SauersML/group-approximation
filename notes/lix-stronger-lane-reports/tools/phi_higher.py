#!/usr/bin/env python3
"""sp-design for the lead: c_q at higher even q, and kappa_top(q,q').

KEY SIMPLIFICATION, so no torus has to be built.  Phi(e_{n(p-1)} (x) iota_n) sits in degree
np, the TOP degree of C_*(Delta^n)^{(x)p}, whose only basis element is [0..n]^{(x)p}; write
it lambda_n . [0..n]^{(x)p}.  For a degree-n cocycle w and ANY n-cycle c = sum n_s s,

    <D_{n(p-1)}(w), c> = lambda_n . (-1)^K . sum_s n_s <w,s>^p
                       = lambda_n . (-1)^K . <w, c>          (mod p, by Fermat x^p = x),

with K = n^2 . p(p-1)/2 the evaluation reordering sign, which is +1 for n even.  So
    c_n = (-1)^{n^2 p(p-1)/2} . lambda_n ,
and the n-torus is needed only to certify that some closed n-manifold carries a degree-n
class with nonzero fundamental evaluation, not for the number.  Products of circles supply
one in every dimension.
"""
import sys
sys.path.insert(0, ".")
from phi_models import (build_phi, top_coeff, sym, deg)


def evalsign(n, p):
    K = (n * n) * (p * (p - 1) // 2)
    return (-1) ** (K % 2)


if __name__ == "__main__":
    cases = [(3, [1, 2, 4, 6]), (5, [1, 2, 4]), (7, [1, 2])]
    if len(sys.argv) > 1:
        p = int(sys.argv[1])
        cases = [(p, [int(a) for a in sys.argv[2:]])]
    for p, ns in cases:
        nmax = max(ns)
        amax = nmax * (p - 1)
        print("=" * 66, flush=True)
        print(f"p = {p}, building Phi on Delta^0..Delta^{nmax}, a <= {amax}", flush=True)
        try:
            phi = build_phi(p, nmax, amax, verbose=True)
        except AssertionError as e:
            print(f"  FAILED: {e}", flush=True)
            continue
        c = {}
        for n in ns:
            lam = top_coeff(phi[n].get(n * (p - 1), {}), n, p)
            cn = (lam * (1 if evalsign(n, p) == 1 else p - 1)) % p
            c[n] = cn
            print(f"  n = {n}:  lambda = {sym(lam,p):+d}   evalsign = {evalsign(n,p):+d}"
                  f"   c_{n} = {sym(cn,p):+d}   ({'NONZERO' if cn % p else 'ZERO'})",
                  flush=True)
        # multiplicativity checks
        for (q, qq) in [(1, 1), (2, 2), (2, 4), (4, 4), (2, 6)]:
            if q in c and qq in c and (q + qq) in c and c[q] % p and c[qq] % p:
                kap = (c[q + qq] * pow(c[q] * c[qq] % p, p - 2, p)) % p
                pred = (-1) ** ((q * qq * ((p - 1) // 2)) % 2)
                print(f"    kappa_top({q},{qq}) = c_{q+qq}/(c_{q} c_{qq}) = {sym(kap,p):+d}"
                      f"   predicted (-1)^(q q' (p-1)/2) = {pred:+d}"
                      f"   {'MATCH' if sym(kap,p) == pred else 'MISMATCH'}", flush=True)
