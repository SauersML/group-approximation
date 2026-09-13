---
rg: 2
id: effective-free-group-kazhdan-lef-type-is-pi01
kind: claim
title: On effectively closed minimal topologically free free-group subshifts, whether the Kazhdan elementary groups are LEF in every rank is a Pi-zero-one property of the index, and its failure is Sigma-zero-one
distinct_from:
  lef-of-finite-presentations-is-pi2-complete: that is LEF recognition over all finite presentations, Pi-zero-two complete; this is the LEF type of one dynamically defined family of Kazhdan groups, which the paradox/measure dichotomy lowers to Pi-zero-one.
  free-group-cantor-elementary-group-lef-iff-invariant-measure: that is the group-level dichotomy for all minimal topologically free free-group Cantor systems; this is its arithmetical position for effectively presented ones.
artifacts:
  - research/artifacts/un-open-6-tarski-complexity-2026-09-13.md
---

**ESTABLISHED** (unreviewed; route `effective-free-group-kazhdan-lef-type-is-pi01-proof`, which requires the
unreviewed dichotomy nodes as they stand).

**Setting.** `2 ≤ r < ∞`, `A` a finite alphabet, `q` a prime power. For an index `e`, `X_e ⊆ A^(F_r)` is the
effectively closed subshift of `effective-subshift-invariant-measure-existence-is-pi01`, and
`R_e = LC(X_e, F_q) ⋊ F_r`. The **promise class** is `𝒫 = {e : X_e is nonempty, minimal and topologically free}`.

**Claim.** Let `P = {e : X_e carries an F_r-invariant Borel probability measure}`, a `Π⁰₁` set. For every `e ∈ 𝒫`:
1. `R_e` is finitely generated as a ring, so `EL_N(R_e)` has property (T) for `N ≥ 3`;
2. `e ∈ P` iff `EL_N(R_e)` is LEF for every `N ≥ 3`;
3. `e ∉ P` iff there is `n ≥ 1` such that every homomorphism from `EL_N(R_e)` to an MF group is trivial for all
   `N ≥ 2n`.

So on `𝒫` the LEF type of these Kazhdan groups is the `Π⁰₁` predicate `P`, and the non-MF type is its `Σ⁰₁`
complement. Equivalently, by Tarski, `[X_e]` is paradoxical in the type semigroup iff `e ∉ P`.

**Scope.**
- This is an upper bound on `𝒫`. Membership in `𝒫` itself (minimality, topological freeness) is not claimed to be
  decidable; the statement is a promise-problem classification.
- Hardness on `𝒫` is `effective-free-group-kazhdan-lef-type-is-pi01-complete` (open).
- Contrast: LEF on finite presentations is `Π⁰₂`-complete (`lef-of-finite-presentations-is-pi2-complete`). Here the
  dichotomy replaces "for every finite window there is a finite model" by "for every radius the pattern-frequency LP
  is feasible".
- Model tests: `F_r ↷ ∂F_r` (paradoxical; `e ∉ P`; no MF quotient, the headline
  `boundary-action-elementary-simple-kazhdan-not-mf`); uniquely ergodic Toeplitz `F_r`-subshifts (`e ∈ P`; LEF,
  `toeplitz-free-group-elementary-groups-are-lef-kazhdan`).

**Review (un-verify, 2026-09-13): PASS.** `χ_{x(g)=a} = u_g χ_{x(1)=a} u_g⁻¹` gives finite generation over `F_q` and (T); the measure side uses the reviewed `free-group-crossed-product-matricial-iff-invariant-measure` and `residually-finite-actions-give-matricial-crossed-products` (PASS by un-verify-measure); the paradox side uses the reviewed canonical no-invariant-measure node; both biconditionals follow on the promise class. See `research/artifacts/un-review-2026-09-13-part9.md` §1.
