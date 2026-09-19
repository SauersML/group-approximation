---
rg: 2
id: thompson-f-ramsey-radius-single-gap-below-reiter-radius
kind: claim
title: In Thompson's F, the coarse Reiter radius is not bounded by any bounded tower wrapped around one composition of the Ramsey function (RGAP₁)
refuted_by:
  - thompson-f-coarse-reiter-radius-is-one-ramsey-call-away
  - thompson-f-amenability-radii-collapse-to-one-tower-degree
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

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-f-last1, calibration, last-mile audit).** Stated as **REFUTED**. It was
  wired by `refuted_by` to `thompson-f-coarse-reiter-radius-is-one-ramsey-call-away` (primary) and to
  `thompson-f-amenability-radii-collapse-to-one-tower-degree`, whose derivation runs through the primary refuter. This
  answers need 6d2c5b22. The companion wiring on ¬AMP is held by swarm-0917-w16-w16-f-pull.
  - *What was checked.* The quantities are the same: `S = {x_0, x_1}`, balls in `S ∪ S⁻¹`, Moore's `R` at threshold
    1/2, and `CR` at ℓ¹ threshold 1. An independent referee pass found no gap in these steps:
    - Steps 1, 3, 5, 6 and 7 of `thompson-f-coarse-reiter-radius-is-one-ramsey-call-away-proof`. This includes:
      - Lemma S at threshold 3/2: `10√(2 ln 4/278) < 0.9988`;
      - the rerun of `coarse-ball-invariance-gives-fine-reiter-measures`, where only Step 1 sees the threshold and
        `c_k ≥ 1/4` gives `ρ_K ≥ 4^{−1/K}`;
      - the error budget `1/2 + 1/8 + 1/8 = 3/4` in Step 5;
      - the minimax step, the only quantifier exchange.
    - Step 8, the CRE derivation, line by line.
  - *Explicit negation (CRE(E)).* Let `a = ⌈log₂ A⌉`, with `A = max(2A_1, A_2, A_1+278)` from Step 7. Then every
    `E ≥ 3 + ⌈log₂(1668 + a)⌉` satisfies `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N ≥ 1`. The inequalities that carry it:
    - *Inner argument.* `exp_{E−1}(N) ≥ 2^{N+E−2} ≥ 2^{E−3}N² ≥ 1668N² + a`, using `2^{N+1} ≥ N²`. So
      `exp_E(N) ≥ 2^a·8^{556N²} ≥ A·6^{556N²}`.
    - *Outer argument.* Put `y = R(exp_E(N)) ≥ N`, using `R(n) ≥ n` because `F` is infinite. Then
      `CR(N) ≤ Ay + AN² ≤ 2Ay² ≤ 2^{a+1+2y}`.
    - *Tower step.* `2^{y+E−2} ≥ 2^{E−2}(1+y) ≥ a + 1 + 2y`, so `CR(N) ≤ 2^{2^{y+E−2}} ≤ exp_E(y)`.
    - *Infinite values.* The case `y = ∞` is trivial, and so is non-amenable `F`, where both sides are `∞` and the
      strict inequality of RGAP₁ fails.
  - *Graph effect.* Two routes are dead:
    - `thompson-f-amenable-via-single-ramsey-reiter-gap` has a refuted premise;
    - `thompson-f-single-ramsey-reiter-gap-via-costly-amplification` has a refuted target. Its premise ¬AMP is refuted
      by the same theorem, so this is no contradiction.
  - *Where it dies (class kill).* The invariant is the tower degree of `CR_F` relative to `R_F`. The one-call theorem
    puts it at 0 up to the exponential window `A·6^{556M²}`. So every member of the Ramsey gap family dies at the
    comparison step "`CR` is not elementary in `R`": RGAP₁, RGAP₂, ¬AMP, SFG and PGAP_1. The argument is specific to `F`
    only through the self-wreath embedding `(F≀Z)×Z ≤ F`, so the `F_2` calibration is untouched.
  - *Last-mile audit of the root after this.* Every route into `thompson-f-is-amenable` that is still OPEN now has a
    last hole that is root-equivalent or stronger:
    - dyadic extensive amenability, and inverted-orbit confinement;
    - Jones-subgroup co-amenability;
    - the exotic co-amenable subgroup, whose P1 under the root is the negation of Brin–Sapir.
    So the root has no genuine last mile left in the graph.
