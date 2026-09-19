---
rg: 2
id: spherical-relation-defect-pairs-small-chord
kind: claim
title: Tight spherical shadowing turns a multiplication defect into a short chord between the conflicting indices
distinct_from:
  hs-defect-is-mean-square-sphere-displacement: that identity converts matrix Hilbert--Schmidt defect into average pointwise unitary displacement; this theorem starts after geometric matchings have been selected and bounds the distance between the two discrete output indices of a relation.
  spherical-one-shared-map-relation-extension: that theorem forces a relation to hold exactly by defining one new map from the other two; this theorem allows all three maps to have been chosen independently and only controls their geometric disagreement.
artifacts:
  - research/artifacts/hyperlinear-cycle-synchronization-bypasses-2026-08-21.md
---

Let `U_g,U_h,U_k in U(d)`, let `x_1,...,x_N` be points on the unit sphere,
and suppose partial maps `sigma_g,sigma_h,sigma_k` geometrically shadow the
three unitaries at radius `rho` wherever the displayed values are defined:

```text
||U_s x_j-x_(sigma_s(j))|| <= rho.                     (SRC1)
```

For a root `i` such that `sigma_h(i)`, `sigma_g(sigma_h(i))`, and
`sigma_k(i)` are defined, assume also

```text
||(U_g U_h-U_k)x_i|| <= zeta.                          (SRC2)
```

Then the two discrete outputs of the tested relation satisfy

```text
||x_(sigma_g sigma_h(i))-x_(sigma_k(i))||
 <= 3 rho + zeta.                                      (SRC3)
```

Consequently, after applying
`hs-defect-is-mean-square-sphere-displacement` and discarding the vanishing
set of roots on which a fixed pointwise threshold fails, every Hamming
mismatch left by independently chosen tight spherical matchings is carried by
a uniformly short geometric chord.