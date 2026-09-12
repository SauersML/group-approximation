---
rg: 2
id: atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat-proof
kind: route
title: Select one cyclic fixed space from each translated A4 tangent sum
target: atlas-fourteen-shifted-tangent-spaces-have-an-s3-flat
requires:
  - atlas-a4-packet-centralizer-product-compiler
  - atlas-a4-rank-three-core
artifacts:
  - experiments/atlas_a4_core_tangent_transversality.py
---

For a shifted cell `D=C(g_1) R C(g_2)`, differentiate

```text
exp(tX) R exp(tY)
```

at zero and right-multiply by `R^-1`.  Here `X` commutes with `rho(g_1)` and
`Y` commutes with `rho(g_2)`, so the translated tangent is exactly

```text
Fix(Ad rho(g_1))+Fix(Ad rho(Rg_2R^-1)).
```

This proves `(A4-TAN-1)` without choosing gauges at different edges.

The companion exact `F_2` audit extracts the eight distinct retained pairs.
Among the `2^8` ways to choose one endpoint from each pair, the generated
subgroup orders have distribution

```text
6:1, 24:4, 96:2, 168:27, 192:2, 1344:58, 20160:162.
```

The unique order-six choice is the four displayed matrices, repeated across
the eight edges.  Exact subgroup closure gives order six, and the elements
include orders two and three with the usual inversion action, hence the group
is `S3`.  A vector fixed by all of `L` is fixed by the chosen endpoint at each
edge and therefore belongs to the corresponding summand of every `S_e`.  This
proves `(A4-TAN-3)`.

For completeness, adjoint left action on a matrix unit `E_(x,y)` preserves
the relative coordinate `x^-1y`.  Each coordinate is one copy of the left
regular `A8` representation.  Its `L`-fixed dimension is the number of left
`L`-orbits, `[A8:L]=3360`, and external amplification simply tensors this
space.  The diagonal operator `i 1_(ell2(L))` is fixed under left translation
by `L`; it cannot be fixed by all of `H`, since left `H`-invariance of its
support would imply `H L=L`, hence `H subseteq L`.  This proves the strict
failure of `(A4-TAN-4)`.

The MSI spectral calibration is supplementary rather than part of the proof.
It verifies that every edge subgroup is `A4`, every edge tangent sum has
dimension `15120`, and a constant-orthogonal alternating-projection sample
stabilizes at nonzero norm, agreeing with the exact flat.  The exact endpoint
subgroup computation, not the floating-point spectrum, certifies the claim.
