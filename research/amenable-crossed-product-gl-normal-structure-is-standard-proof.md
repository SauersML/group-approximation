---
rg: 2
id: amenable-crossed-product-gl-normal-structure-is-standard-proof
kind: route
title: Ring simplicity from the Steinberg criterion, then Stepanov's Theorem 4.4 with condition (b) from pair dependence
target: amenable-crossed-product-gl-normal-structure-is-standard
requires:
  - amenable-crossed-products-meet-stepanov-condition-b
  - stepanov-linear-dependence-standard-normal-structure
  - steinberg-algebra-simple-iff-minimal-effective
artifacts:
  - research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md
---

1. **`R` is simple.** `R` is the Steinberg algebra over `K` of the transformation groupoid `Γ ⋉ X`, via
   `χ_({γ}×U) ↦ e_(γU) u_γ` (Beuter–Gonçalves, J. Algebra 497 (2018), as in `minimal-subshift-algebra-is-simple-lef-ring`).
   - `Γ ⋉ X` is Hausdorff and ample, because `Γ` is discrete and `X` is totally disconnected.
   - It is minimal because the action is minimal.
   - It is effective because the action is topologically free: the interior of the isotropy bundle is the unit space
     exactly when every `γ ≠ 1` has a fixed-point set with empty interior.
   - So `R` is simple by `steinberg-algebra-simple-iff-minimal-effective`, and its only proper two-sided ideal is `0`.
2. **Condition (a) of Stepanov's Theorem 4.4.** For `I = 0` it reads `[GL(n,R,0), E(n,R)] = E(n,R,0) = {1}`, which is
   true.
3. **Condition (b)** for `I = 0` is item 2 of `amenable-crossed-products-meet-stepanov-condition-b`.
4. **Sandwich.** By `stepanov-linear-dependence-standard-normal-structure`, Theorem 4.4, part (1.6)(3) holds. Every
   `H ≤ GL(n,R)` normalized by `E(n,R)` satisfies `E(n,R,I) ≤ H ≤ C(n,R,I)` for a unique ideal `I`, and the proof on
   p. 2152 ends with exactly this sandwich.
   - `I = R` gives `H ⊇ E(n,R)`.
   - `I = 0` gives `H ≤ C(n,R,0)`, the centre of `GL(n,R)`, namely `Z(R)^× I_n`.
5. **Simplicity of `EL_n(R)/Z`.** A normal subgroup of `EL_n(R) = E(n,R)` is normalized by `E(n,R)`. So it is central
   in `GL_n(R)`, hence contained in `Z(EL_n(R))`, or it is everything.
