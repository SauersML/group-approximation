---
rg: 2
id: unperforated-paradox-makes-steinberg-purely-infinite
kind: claim
title: For a minimal effective ample groupoid with almost unperforated type semigroup and no invariant measure, the Steinberg algebra is properly purely infinite over every field and its elementary groups have no MF quotient from rank two
distinct_from:
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that gives a properly infinite multiple of the unit and the threshold 2n with no hypothesis on the type semigroup; this assumes almost unperforation, pushes the paradox down to the unit itself, and gets proper pure infiniteness of the algebra and the threshold two.
  rainone-sims-type-semigroup-dichotomy: that is the C*-dichotomy, purely infinite or stably finite for C*_r(G); this is the algebraic dichotomy for the Steinberg algebra over an arbitrary countable field, where the second branch yields an invariant measure rather than stable finiteness.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**ESTABLISHED** (unreviewed; proof route `unperforated-paradox-makes-steinberg-purely-infinite-proof`).

Let `𝒢` be a minimal, effective, Hausdorff, ample, second countable groupoid with compact unit space
`X`, whose type semigroup `S(𝒢)` is almost unperforated, and let `k` be a countable field,
`R = A_k(𝒢)`. Consider

1. `X` carries a `𝒢`-invariant Borel probability measure;
2. `R` is simple and **properly purely infinite**, `R` is not directly finite, and every homomorphism
   from `EL_n(R)` to an MF group is trivial for every `n ≥ 2`.

- **Exhaustive, over every field.** If (1) fails then (2) holds. So at least one of (1), (2) is true.
- **Exclusive for `k ⊆ ℂ`.** An invariant measure gives a faithful Sylvester matrix rank function
  (`invariant-measure-gives-rank-function-in-char-zero`), hence stable finiteness, which contradicts
  (2).
- **Exclusivity NOT claimed in characteristic `p`.** Excluding the ring properties of (2) in the
  presence of an invariant measure needs *invariant measure ⟹ stably finite*, which is open and at
  least Kaplansky-hard (`invariant-measure-gives-rank-function-any-field`,
  `measure-side-stable-finiteness-contains-char-p-kaplansky`). What is exclusive over every field is
  only the groupoid-level alternative, an invariant measure versus `θ` paradoxical
  (`algebraic-tarski-for-steinberg-algebras` step 3), because `ι` is not known to reflect paradox
  (`type-semigroup-reflects-paradox-of-steinberg-algebra`).

*Correction, 2026-09-13.* The landing 991380d00d stated "exactly one of" for every field. un-verify-3
found the overclaim: in characteristic `p`, step 3 excludes an invariant measure only against `θ`
paradoxical, not against the ring properties of (2).

**What is gained over the unconditional paradox branch.** `no-invariant-measure-steinberg-elementary-no-mf-quotient`
derives `2n[1] ≤ n[1]` for some `n` and the threshold `N ≥ 2n`. Almost unperforation pushes the
paradox down to the unit itself, `2[1] ≤ [1]`, giving the best possible threshold `n ≥ 2` and, through
Larki's characterization, proper pure infiniteness of the algebra rather than only the failure of
stable finiteness.

**On the threshold.** `2[1] ≤ [1]` gives `s_1, s_2, t_1, t_2 ∈ R` with `t_i s_j = δ_ij 1`, and then
`1 − s_1 t_1` is full because `t_2 (1 − s_1 t_1) s_2 = t_2 s_2 = 1`. So the established
`full-defect-ring-non-mf-at-rank-two` gives triviality from rank two directly; simplicity of `R` is
not needed for fullness.

**Model tests.**
- Cuntz groupoid `𝒢_2`: `S(𝒢) = {0, θ}` with `2θ = θ`, almost unperforated, branch 2. Recovers that
  `L_k(1,2)` is purely infinite with no MF quotient for its elementary groups.
- Minimal subshift over `Z`: an invariant measure exists, branch 1. The theorem correctly says nothing
  about pure infiniteness there, consistent with the Pestov 9.1 group being LEF.
- Boundary action `∂F_d ⋊ F_d`: no invariant measure, branch 2, agreeing with
  `boundary-action-elementary-simple-kazhdan-not-mf`.
- Boldrini–Prasad minimal `F_∞` actions: `S(𝒢)` is **not** almost unperforated, so the hypothesis
  fails and neither branch is forced. That is exactly the middle region of the UN program.

**Review (un-verify-3, 2026-09-13): PASS after repair.** Part 1 found a GAP: "exactly one" was asserted in characteristic p, and the route required only the rank-four node. un-tarski's repair (0156bb3f0a) re-checked: exhaustive over every field; exclusive for `k ⊆ ℂ` via `invariant-measure-gives-rank-function-in-char-zero`; no exclusivity claimed in characteristic `p`. The route now requires `full-defect-ring-non-mf-at-rank-two`. From `2[1] ≤ [1]` there are `s_1, s_2, t_1, t_2` with `t_i s_j = δ_ij`, so `t_2(1 − s_1t_1)s_2 = 1` and the defect is full. `research/artifacts/un-review3-2026-09-13-part2.md` §1.
