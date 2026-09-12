---
rg: 2
id: sp21-pro-p-finite-rank-from-congruence-property
kind: route
title: A finite congruence kernel makes every pro-p congruence kernel finite, hence every pro-p completion finite rank
target: sp21-lattice-pro-p-completions-have-finite-rank
requires:
  - sp21-lattice-has-congruence-subgroup-property
  - sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel
---

Assume `sp21-lattice-has-congruence-subgroup-property`, so
`ker(Γ̂ -> Γ̄)` is finite.

1. **Pro-p kernels are finite.** For `Δ <= Γ(p)` of finite index, the pro-p
   congruence kernel `ker(Δ̂_p -> Δ̄_p)` is the image of the congruence kernel of
   `Δ` in the maximal pro-p quotient. `Δ` is again a finite-index subgroup of an
   arithmetic group with the property, so that congruence kernel is finite, and
   so is its image.
2. **Finite rank.** By the easy direction of
   `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`, `Δ̂_p` has finite
   rank.
