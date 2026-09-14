---
rg: 2
id: subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit-proof
kind: route
title: A G-set isomorphism is additive by pointwise-stabilizer fixed sets, diagonal by root-subgroup fixed sets, R-linear by e_12 equivariance, and it preserves LC(X)-weights
target: subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit
requires: [subshift-el3-acts-two-transitively-on-orbit-modules, subshift-el3-has-continuum-many-maximal-subgroup-classes]
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part2.md
---

Full proof: artifact part 2.
- **Orbit ⇒ module.** `δ_n ↦ δ_{n−m}` is an isomorphism `V_x → V_{T^m x}`.
- **Module ⇒ G-set.** Apply the isomorphism coordinatewise.
- **G-set ⇔ conjugate stabilizers.** This holds for transitive actions.
- **G-set ⇒ module.** Let `φ : Ω_x → Ω_y` be an equivariant bijection.
  - (a) By independent-triple transitivity (`subshift-el3-acts-two-transitively-on-orbit-modules`, k = 3), the pointwise stabilizer of `v ≠ w` fixes exactly `v, w, v+w`. So `φ(v+w) = φv + φw`, and `φ` is linear.
  - (b) The common fixed points of `e_12(R)` and `e_13(R)` form `V e_1 ∖ 0`, and likewise for `e_2` and `e_3`. So `φ = diag(φ_1, φ_2, φ_3)`.
  - (c) Equivariance under `e_12(r)` gives `φ_1(r v) = r φ_2 v`. Taking `r = 1` gives `φ_1 = φ_2`, so `φ_1` is `R`-linear.
- **Module ⇒ orbit.** Every `f ∈ LC(X,F_2)` acts on `δ_n ∈ V_x` by the scalar `f(T^n x)`. An `R`-isomorphism sends `δ_n` to a nonzero vector with the same eigenvalues, whose support positions `m` satisfy `T^m y = T^n x`. ∎
