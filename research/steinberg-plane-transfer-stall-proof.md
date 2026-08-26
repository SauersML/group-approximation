---
rg: 2
id: steinberg-plane-transfer-stall-proof
kind: route
title: Distinguish the usable two-endpoint relation from naïve Möbius iteration
target: steinberg-plane-transfer-stalls-at-large-primes
requires:
  - steinberg-zero-marginal-kills-b-minus-one-plane
  - steinberg-zero-plane-transfer-closes-p-five
---

The proof of `(SPT1)` does not say that a zero plane `B` directly makes
`T(B)=4B/(1-4B)` zero.  It first uses `B` to remove the `h^(-1)r` term and
then gives an equivalence between `q`-invariance on

```text
x=4B                  and                  x/(1-x).    (SPTSP1)
```

Thus one endpoint of `(SPTSP1)` must already be a zero plane before the
other can be added.  The exceptional case `x=1` directly adds that
pre-plane.

Start with `Z_0={-1}`.  For `B=-1`, the two generic endpoints are

```text
-4                     and                  -4/5.      (SPTSP2)
```

The first equals the known plane `-1` exactly in characteristic three.
The second could equal `-1` only if `4=5`, which is impossible.  The
exceptional condition `-4=1` holds exactly in characteristic five.
Consequently no first new plane is available for any odd `p>=7`, while
the prime-three and prime-five closures are precisely the already proved
exceptional cases.

For comparison, naïvely iterating the fractional-linear expression would
give

```text
1/T(B)=1/(4B)-1,
T^n(-1)=3*4^n/(1-4^(n+1))                              (SPTSP3)
```

projectively.  That orbit has length governed by `ord_p(4)` and includes
the point at infinity; it is not the logical propagation relation supplied
by `Y`.  Formula `(SPTSP3)` therefore cannot be used to bypass the missing
known endpoint.
