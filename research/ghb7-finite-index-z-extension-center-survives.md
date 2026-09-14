---
rg: 2
id: ghb7-finite-index-z-extension-center-survives
kind: claim
title: Some finite-index subgroup of GHB_2(7) has a central Z-extension with finite abelianization whose centre survives at unbounded orders in finite quotients
distinct_from:
  sl3-polynomial-finite-index-z-extension-center-survives: that is the same profinite premise for congruence subgroups of SL_3(F_q[t]); this asks it for finite-index subgroups of the hyperbolic Kazhdan group GHB_2(7)
  hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class: that derives a persistent degree-two class from stability of a hyperlinear hyperbolic Kazhdan group; this asks for the opposite profinite behaviour, a centre visible at unbounded orders, which destroys stability
---

**OPEN.** There are:
- a finite-index subgroup `K` of `G = G_{HB_2}(7)`;
- a central extension `1 → Z = ⟨z⟩ → K~ → K → 1` where `K~` has finite abelianization;

such that the order of the image of `z` in finite quotients of `K~` is unbounded.

**Consequence if true.** `G` is not flexibly HS stable, by route
`ghb7-instability-via-visible-central-extension`. That closes `ghb7-flexibly-hs-stable`, hence
`ghb7-one-edge-holonomy-absorption` and (EM) for this triangle.

## Attempts

- **The first requirement holds at the congruence kernel (standard facts, not re-read at source).**
  - Let `H = Ker(ψ)` from `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`. It has finite
    index, property (T) and `b_2(H;Q) >= 1380`.
  - By universal coefficients `H^2(H;Z) → Hom(H_2(H;Z), Z)` is onto, and the target has positive
    rank. So some class `c` evaluates nontrivially on `H_2(H;Z)`.
  - For the central extension `H~_c`, the exact sequence
    `H_2(H;Z) → Z → H_1(H~_c) → H_1(H) → 0` has connecting map the evaluation of `c`. Its image is
    `nZ` with `n ≠ 0`, so `H_1(H~_c)` is an extension of the finite group `H_1(H)` by a quotient of
    `Z/n`, hence finite.
  - So central `Z`-extensions of `H` with finite abelianization exist. What is open is survival of
    the centre.
- **Survival is inflation at unbounded orders (elementary).** Let `Q` be a finite quotient of `K~` in
  which `z` maps to `z̄` of order `n`, and put `Q̄ = Q/⟨z̄⟩`. The map `K~/⟨z^n⟩ → Q` is a map of
  central extensions over `K → Q̄` that is the identity on `Z/n`. So the class of `K~` reduced mod `n`
  is inflated from `H^2(Q̄; Z/n)`. The claim therefore asks that a non-torsion class be inflated from
  finite quotients at unbounded orders, a goodness-type property of `K` in degree two.
- **Calibration.**
  - The failure model is Deligne's cover of `Sp_(2n)(Z)`: a Kazhdan central `Z`-extension whose
    centre has bounded order in finite quotients (`deligne-universal-cover-lattice-is-non-rf-kazhdan`).
  - If `G` is hyperlinear, stability of `G` forces a persistent degree-two class and non-goodness
    (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`). This claim is the opposite
    profinite behaviour.
- **Not done.** No finite quotient of any `K~` was computed, and no finite-index `K` smaller than `H`
  with a real degree-two class was exhibited. By `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`,
  a torsion-free `K` of index `m` has `χ(K) = 1381·m/2401 > 0`, so every torsion-free finite-index
  subgroup has real degree-two classes. Those arise as kernels of finite quotients injective on the
  vertex groups (`cckw-ghb2-kms-group-structure`, item 4).
