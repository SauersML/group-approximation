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

For comparison, direct Möbius iteration is strictly stronger than the
proved rule.  For `p!=3`, put

```text
z(B)=4B/(4B+3).
```

Then direct substitution gives

```text
z(T(B))=4z(B),
T^n(-1)=3*4^n/(1-4^(n+1)).                             (SPTSP3)
```

The fixed points are `0` and `-3/4`, corresponding to `z=0,infinity`,
while `z(-1)=4`.  Thus the direct orbit has exactly `ord_p(4)` elements
and never reaches the nonzero fixed plane `-3/4`.  It is not the logical
propagation relation supplied by `Y`, and even this stronger, unjustified
orbit would not kill every nonzero plane.
