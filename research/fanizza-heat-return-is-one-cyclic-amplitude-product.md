---
rg: 2
id: fanizza-heat-return-is-one-cyclic-amplitude-product
kind: claim
title: One cyclic amplitude product is enough to return the Fanizza heat filter
distinct_from:
  fanizza-heat-filter-one-sided-return: that asks for a group extension returning the filtered mark; this is the exact scalar endpoint the finite-matrix decoder must produce.
  trace-cyclic-rank-mismatch-checksum: that compares two projections/ranks; this compares a source projection with the positive amplitude square of a strict heat-filter contraction.
  compressed-reflection-kills-even-cesaro-mark: that uses one compressed reflection and its powers; this uses the independently established heat-filter norm decay.
---

Fix a Fanizza instance and use the accelerated real polynomial filter.  Put

```text
B_t=D_R p_t(H_m),
A_t=B_t^* B_t=p_t(H_m) D_R p_t(H_m).                  (HAP1)
```

In every NONHALT representation,

```text
0<=A_t,
tr_d(A_t)=||B_t||_(2,d)^2
          <=||B_t||^2
          <=C_m/(4t^2).                               (HAP2)
```

Let `P in M_d(C)` be a projection and let `X,Y` be arbitrary matrices.  If

```text
||YX-P||_2<=epsilon,
||XY-A_t||_2<=delta,                                  (HAP3)
```

then finite-dimensional trace cyclicity gives

```text
tr_d(P)<=epsilon+delta+C_m/(4t^2).                    (HAP4)
```

Indeed `tr(YX)=tr(XY)` and the normalized trace functional has HS norm one.
The power filter gives the alternative remainder `C_m/(2t+1)`.

Consequently a matrix-only group-word decoder producing `(HAP3)` for every
fixed virtual depth `t`, with errors tending to zero at fixed `t`, collapses
the returned carrier by taking the microstate limit first and `t->infinity`
second.  If the fixed group-algebra mark is controlled by

```text
||p_m(U)||_2^2<=C tr_d(P)+o(1),                       (HAP5)
```

this is exactly `fanizza-heat-filter-one-sided-return`.

HALT completeness is compatible.  In the perfect quotient `H_m=0`, hence
`B_t=A_t=D_R` for every `t`; take `P=D_R` and `X=Y=D_R`, and then countably
amplify inside a properly infinite ambient representation.  Thus the scalar
endpoint itself does not kill the HALT signal.

The remaining word “matrix-only” is load-bearing.  If `P,X,Y,A_t` were fixed
group-algebra matrices and `(HAP3)` with zero error followed functorially
from the relators, the same products would exist in the regular finite
von Neumann algebra.  Cyclicity plus `(HAP2)` for arbitrarily large `t` would
force the nonzero regular carrier `P` to vanish.  Therefore the decoder must
use finite coordinate multiplicity/rank to obtain the two products; a Julia,
Steinberg, Toeplitz, or Leavitt block identity valid in all tracial
representations is forbidden.

This is the smallest current amplitude-sensitive return target.  It replaces
an unspecified “returned copy of the filtered carrier” by two explicit
products and one scalar estimate.
