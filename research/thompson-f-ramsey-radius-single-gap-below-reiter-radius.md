---
rg: 2
id: thompson-f-ramsey-radius-single-gap-below-reiter-radius
kind: claim
title: In Thompson's F, the coarse Reiter radius is not bounded by any bounded tower wrapped around one composition of the Ramsey function (RGAP₁)
distinct_from:
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂, with two compositions of R, and implies ¬AMP; this is RGAP₁, with one composition, which is implied by ¬AMP and is the weakest statement of the Ramsey family that still implies amenability.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, about the fine one-function radius against R; this compares CR with R directly and is equivalent to ¬AMP ∨ SFG.
  thompson-f-second-test-function-costs-more-than-any-tower: that is SFG, CR against the one-function radius ψ; this is CR against R, and SFG is one of its two disjuncts.
  thompson-f-folner-function-exceeds-every-tower: that says CR is not elementary; this says CR is not elementary relative to R, which is a statement that R is small.
---

**OPEN.** Notation is as in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`: `S = {x_0, x_1}`,
`R = R_{F,S}`, `CR` the coarse Reiter radius, values in `[0, ∞]` with `exp_E(∞) = ∞`.

**Statement (RGAP₁).** For every integer `E ≥ 0` there is an integer `N ≥ 1` with

`CR(N) > exp_E(R(exp_E(N)))`.

Its negation is CRE: some `E` has `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N`. In the notation of
`thompson-f-ramsey-radii-in-the-elementary-degree-order`, RGAP₁ is `CR ⋠ R`.

**It implies amenability of F.** The strict inequality forces `R(exp_E(N_E)) < ∞` for every `E`, so `R < ∞`
everywhere, by monotonicity. Moore's Theorem 1.3 (2)⇒(4) then applies. This is Corollary 3 of the sandwich, and
the route `thompson-f-amenable-via-single-ramsey-reiter-gap` records it.

**Where it sits.** It is implied by each of:
- RGAP₂ (`thompson-f-ramsey-radius-double-gap-below-reiter-radius`);
- ¬AMP (`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`);
- SFG (`thompson-f-second-test-function-costs-more-than-any-tower`);
- PGAP_1 (`ramsey-functions-are-pairwise-reiter-radii`).

It is exactly ¬AMP ∨ SFG (`thompson-f-ramsey-radii-in-the-elementary-degree-order`, clause 5). So it is the
weakest of these statements, and among them the natural target for the root.

**It can fail on its own.** It fails if `R_F` is within a bounded tower of `CR_F`, whether or not `F` is amenable.
If `F` is not amenable, both sides are `∞` and the statement is false. If `F` is amenable with CRE, every member of
the Ramsey family dies at once: ¬AMP, SFG, RGAP₂, PGAP_1 and the route
`thompson-f-amenable-via-costly-ramsey-amplification`. In that case Moore's hope of an elementary `R_F` also dies,
since `CR_F` is non-elementary.

**Known necessary shape.**
- Any proof must place, at some scale, "every single pair of measures on `B_t` is balanced" (`R`, up to thresholds)
  non-elementarily earlier than "one measure is coarsely `B_N`-invariant" (`CR`). See the pair identity and the
  attempts recorded on RGAP₂.
- The CR side is one Rayleigh quotient, by `coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue`.
- `R_F(m) ≥ 2^{m/4−6}`, by `thompson-f-ramsey-radius-is-at-least-exponential`.
- The kills recorded on RGAP₂ were aimed at CRE, the negation of this claim, so they apply here unchanged:
  - selector coding;
  - marker coding;
  - time-shift pairs.
