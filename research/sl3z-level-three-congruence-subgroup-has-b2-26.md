---
rg: 2
id: sl3z-level-three-congruence-subgroup-has-b2-26
kind: claim
title: The level-three principal congruence subgroup Γ(3) of SL_3(Z) has rational Betti numbers (1, 0, 26, 27)
distinct_from:
  sl3z-finite-index-fd-projective-multiplier-is-finite: that leaves open whether any congruence subgroup of SL_3(Z) has b_2 > 0; this decides it, with b_2(Γ(3)) = 26.
  sl3-polynomial-congruence-subgroups-have-large-b2: that is the function-field analogue for SL_3(F_q[t]), conditional on Soulé's domain; this is SL_3(Z) at level 3, unconditional given two literature imports.
  ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2: that is positive b_2 for a hyperbolic Kazhdan group; this is positive b_2 for a higher-rank lattice whose profinite completion is known by the congruence subgroup property.
  sl3z-contains-rfrs-cd2-subgroup-with-positive-b2: that is an infinite-index cd-2 subgroup; this is a finite-index subgroup of cd 3.
  lee-szczarba-level-three-top-cohomology-is-steinberg: that imports b_3 = 27; this adds b_2 from the Euler characteristic.
artifacts:
  - experiments/sl3z-level-three-betti-2026-09-17/tits-quotient-and-euler-count.py
---

**ESTABLISHED (unreviewed).** Let `Γ = Γ(3) = ker(SL_3(Z) -> SL_3(F_3))`. Then

```text
dim_Q H^q(Γ; Q) = 1, 0, 26, 27   for q = 0, 1, 2, 3,
dim_Q H^q(Γ; Q) = 0              for q >= 4.
```

Derivation: `sl3z-level-three-b2-euler-count-proof`.

**Integral forms.**
- `H_2(Γ; Z)` has free rank 26, and so does `H^2(Γ; Z)`.
- The image of `H^2(Γ; Z)` in `H^2(Γ; R) ≅ R^26` is a full lattice.
- For every `n >= 1`, the subgroup `H^2(Γ; Z)/n` of `H^2(Γ; Z/n)` has order at least `n^26`.

**Consequences in the graph.**
- **The settings are non-vacuous.** The b_2 > 0 question left open in
  `sl3z-finite-index-fd-projective-multiplier-is-finite` and
  `sl3z-finite-index-z-extension-centres-stay-bounded` now has an instance, `K = Γ(3)`.
- **Degree two fails.** `sl3z-level-three-fails-degree-two-goodness`.

**Not claimed.**
- The torsion of `H^*(Γ; Z)`.
- The Hecke or `SL_3(F_3)`-module structure of `H^2`.
- Any other level.
