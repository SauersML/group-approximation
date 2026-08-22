---
rg: 2
id: atlas-o8m2-has-one-a8-class-with-c3-centralizer
kind: claim
title: O8-(2) has one A8 class, normalized by (3xA8):2 with centralizer C3
artifacts:
  - experiments/atlas_o8m2_a8_carrier_audit.py
  - experiments/atlas-o8m2-a8-carrier-audit.json
distinct_from:
  atlas-o8p2-has-six-triality-a8-classes: the plus-type group splits into six triality classes; the minus-type endpoint fuses its two apparent carrier sources into one class.
  atlas-a8-index-33-to-89-is-orthogonal-sp6: that classifies A8 inside Sp6(2); this computes its fusion and enlarged normalizer in O8-(2).
---

Let `G=O8-(2)`.  It has exactly one conjugacy class of subgroups `A~=A8`.
For every such subgroup,

```text
N_G(A) ~= (3 x A8):2,     |N_G(A)|=120960,
C_G(A) ~= C3,             |A^G|=1632.               (OMC1)
```

The induced automorphism group has order

```text
|N_G(A)/C_G(A)|=40320=|Aut(A8)|,
```

so the ambient normalizer realizes the graph automorphism.  There is no
separate relative-marking parity in the eventual packet screen.

Only two maximal-carrier orders in the ATLAS list are divisible by `20160`:

```text
S6(2), order 1451520;       (3 x A8):2, order 120960. (OMC2)
```

The orthogonal `A8` inside the first carrier and the normal direct-factor
`A8` inside the second fuse in `G`.  Exact incidence is

```text
136 S6(2) carriers; 36 A8s per carrier; 3 carriers per A8. (OMC3)
```

Thus future equality work has one subgroup class and one normalizer
double-coset geometry, not a triality/fusion fork.

