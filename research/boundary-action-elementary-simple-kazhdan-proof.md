---
rg: 2
id: boundary-action-elementary-simple-kazhdan-proof
kind: route
title: Minimal effective boundary groupoid gives a simple ring with local annihilation; the paradox kills every MF quotient
target: boundary-action-elementary-simple-kazhdan-not-mf
requires:
  - paradoxical-steinberg-families-kazhdan-no-mf-quotient
  - steinberg-algebra-simple-iff-minimal-effective
  - steinberg-algebras-have-local-annihilation
  - local-annihilation-makes-projective-el-simple
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

## Why sufficient

`R = A_k(F_d ⋉ ∂F_d)` is the Steinberg algebra of the transformation groupoid. That groupoid is ample
and Hausdorff, and its unit space `∂F_d` is compact and infinite.

1. **Minimal.** Given `w ∈ ∂F_d` and a cylinder `C(u)`, choose a letter `c` that is neither inverse to
   the last letter of `u` nor inverse to the first letter of `w`. At most two of the `2d >= 4` letters
   are excluded. Then `(uc) · w = u c w` is reduced and lies in `C(u)`, so every orbit is dense.
2. **Effective.** For `g != e`, `Fix(g)` has at most two points. For cyclically reduced `g` these are
   `g^(±∞)`, and `Fix(hgh^(-1)) = h Fix(g)`. `∂F_d` has no isolated points, so `Fix(g)` has empty
   interior. So the action is topologically free, and the transformation groupoid is effective.
3. **Simple ring.** By `steinberg-algebra-simple-iff-minimal-effective`, `R` is simple.
4. **Simple group.** By `steinberg-algebras-have-local-annihilation`, `R` has local annihilation. By
   `local-annihilation-makes-projective-el-simple` (`N >= 3`), every normal subgroup of `EL_N(R)` is
   central or everything, so `S_∂` is simple.
5. **Infinite.** `e_12(r) e_12(r')^(-1) = e_12(r - r')` is not scalar for `r != r'`, and `R` is infinite.
   So the images of the `e_12(r)` are pairwise distinct in `S_∂`.
6. **No MF quotient, every countable `k`.** A homomorphism `S_∂ -> H` with `H` MF composes to one on
   `EL_N(R)`. That composite is trivial by (F1) of `paradoxical-steinberg-families-kazhdan-no-mf-quotient`,
   so the homomorphism is trivial. `S_∂` is nontrivial, so it is not MF.
7. **Finitely generated and Kazhdan, finite `k` only.** By the finite-field clause of (F1), `R` is a
   finitely generated ring and `EL_N(R)` is finitely generated and Kazhdan. Both properties pass to
   the quotient `S_∂`. For infinite `k` neither clause is asserted (correction paragraph of the claim).
