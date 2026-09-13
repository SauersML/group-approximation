---
rg: 2
id: unperforated-paradox-makes-steinberg-purely-infinite
kind: claim
title: For a minimal effective ample groupoid with almost unperforated type semigroup, either the unit space carries an invariant measure or the Steinberg algebra is properly purely infinite over every field and its elementary groups have no MF quotient from rank two
distinct_from:
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that gives a properly infinite multiple of the unit and the threshold 2n with no hypothesis on the type semigroup; this assumes almost unperforation, pushes the paradox down to the unit itself, and gets proper pure infiniteness of the algebra and the threshold two.
  rainone-sims-type-semigroup-dichotomy: that is the C*-dichotomy, purely infinite or stably finite for C*_r(G); this is the algebraic dichotomy for the Steinberg algebra over an arbitrary countable field, where the second branch yields an invariant measure rather than stable finiteness.
artifacts:
  - research/artifacts/un-algebraic-tarski-2026-09-13.md
---

**ESTABLISHED** (unreviewed; proof route `unperforated-paradox-makes-steinberg-purely-infinite-proof`).

Let `𝒢` be a minimal, effective, Hausdorff, ample, second countable groupoid with compact unit space
`X`, whose type semigroup `S(𝒢)` is almost unperforated, and let `k` be a countable field,
`R = A_k(𝒢)`. Then exactly one of the following holds.

1. `X` carries a `𝒢`-invariant Borel probability measure.
2. `R` is simple and **properly purely infinite**; `R` is not directly finite; and every homomorphism
   from `EL_n(R)` to an MF group is trivial for every `n ≥ 2`.

The two branches are exclusive and exhaustive by `algebraic-tarski-for-steinberg-algebras` step 3.

**What is gained over the unconditional paradox branch.** `no-invariant-measure-steinberg-elementary-no-mf-quotient`
derives `2n[1] ≤ n[1]` for some `n` and the threshold `N ≥ 2n`. Almost unperforation pushes the
paradox down to the unit itself, `2[1] ≤ [1]`, giving the best possible threshold `n ≥ 2` and, through
Larki's characterization, proper pure infiniteness of the algebra rather than only the failure of
stable finiteness.

**On the threshold.** The printed source is the non-MF paper, `cor:simple-infinite-ring` (tex l.1016):
"If `R` is a countable simple unital ring that is not directly finite, then every homomorphism from
`EL_n(R)` to an MF group is trivial for every `n ≥ 2`." The landed node
`simple-dedekind-infinite-ring-elementary-full-mf-radical` states the same corollary conservatively
from rank four; branch 2 above is therefore certain from rank four and holds from rank two on the
printed statement.

**Model tests.**
- Cuntz groupoid `𝒢_2`: `S(𝒢) = {0, θ}` with `2θ = θ`, almost unperforated, branch 2. Recovers that
  `L_k(1,2)` is purely infinite with no MF quotient for its elementary groups.
- Minimal subshift over `Z`: an invariant measure exists, branch 1. The theorem correctly says nothing
  about pure infiniteness there, consistent with the Pestov 9.1 group being LEF.
- Boundary action `∂F_d ⋊ F_d`: no invariant measure, branch 2, agreeing with
  `boundary-action-elementary-simple-kazhdan-not-mf`.
- Boldrini–Prasad minimal `F_∞` actions: `S(𝒢)` is **not** almost unperforated, so the hypothesis
  fails and neither branch is forced. That is exactly the middle region of the UN program.
