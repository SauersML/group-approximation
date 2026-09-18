---
rg: 2
id: sqrt-scale-unique-games-hardness
kind: claim
title: Sqrt-scale UGC -- for every C there are eta <= 1/C^2 and k making Gap-UG_k[1-eta, 1-C sqrt(eta)] NP-hard
distinct_from:
  unique-games-conjecture: that is the near-1 versus near-0 gap; this is a near-1 versus near-1 gap whose deficit ratio gamma/sqrt(eta) is unbounded. The two are equivalent by sqrt-scale-unique-games-hardness-is-equivalent-to-ugc.
  small-set-expansion-hypothesis: that is expansion hardness, not known to follow from UGC; this is a reformulation of UGC itself at a different soundness scale.
  unique-games-hard-at-completeness-one-half: that is the proved gap with completeness near 1/2; this hypothesis keeps completeness near 1 and asks only for a soundness deficit C sqrt(eta).
---

**OPEN.** Write `Gap-UG_k[c, s]` for the promise problem on bipartite unique
games with alphabet `[k]`, given as edge multisets: YES means `val >= c`, NO
means `val <= s`. The hypothesis is

```text
for every C >= 1 there are eta in (0, 1/C^2] and k such that
Gap-UG_k[1 - eta, 1 - C sqrt(eta)] is NP-hard.
```

Both thresholds are near `1`, and neither needs to be near `0`. The only
requirement is that the soundness deficit `gamma = 1 - s` exceeds the
completeness deficit `eta` by an **unbounded multiple of `sqrt(eta)`**.

**Equivalent to UGC.** See `sqrt-scale-unique-games-hardness-is-equivalent-to-ugc`.
Dinur--Steurer repetition, with a constant number of rounds, turns the sqrt-scale
gap into the root gap, and the root gap trivially gives this one. So the route
`ugc-from-sqrt-scale-unique-games-hardness` reaches the root, and **refuting
this hypothesis refutes UGC**.

**Quantitative shape.**

* **Scale cannot be lowered.** Soundness deficits `gamma = o(sqrt(eta))` are
  useless for repetition. See
  `black-box-repetition-needs-sqrt-scale-soundness-gap`, which uses Raz's odd
  cycle.
* **Alphabet cost.** Hardness at ratio `C` forces `log k >= C^2/(4A^2)`
  unless `NP <= RP`, where `A` is the CMM constant. See
  `sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared`.
* **Linear rung.** Hardness at ratio `R >= 6` gives
  `Gap-UG[1 - eta, 1 - L eta]` hardness with `L = (1 - 1/e) R^2/17` at every
  small scale. This is the squaring law recorded in the equivalence claim. So
  a bounded linear deficit ratio would refute this hypothesis.

**What would falsify it.** Unless `NP <= BPP`, either of the following refutes
the hypothesis:

* a randomized polynomial-time algorithm that, for some absolute `C_0`, finds
  value `> 1 - C_0 sqrt(eta)` with probability `>= 2/3` on every
  `(1-eta)`-satisfiable unique game, **uniformly in `k`**;
* a `BPP` algorithm for `Gap-UG_k[1-eta, 1-L eta]` for one fixed `L` and all
  `k` and `eta`.

The basic SDP does not give the uniform algorithm. Khot--Vishnoi gaps have SDP
value `1 - eta` and integral value `k^-Omega(eta)`.

## Attempts

* **Direct from the 2-to-2 theorem** (swarm-0917, `e-ugc-pull-logic`).
  - *Construction.* Start from `unique-games-hard-at-completeness-one-half`,
    bipartize (each constraint in both orientations at half weight), and dilute
    with identity edges (Step 4 of `ugc-sqrt-scale-equivalence-proof`).
  - *Result.* This gives NP-hard gaps `1 - rho(1+eps)/2` versus
    `1 - rho(1-2eps)`. Their deficit ratio `gamma/eta` tends to `2`. At the
    sqrt scale that is `C = 2 sqrt(eta) -> 0`, far from unbounded `C`.
  - *Where it dies.* The one-half completeness wall. Dilution preserves the
    linear deficit ratio and cannot raise it, while the squaring law needs
    ratio `R >= 6` at the sqrt scale.
  - *Related work.* The padding invariant is being developed separately by
    `swarm-0917-w6-w6-ugc-break`.
* **Linear-loss dictatorship tests plus repetition.**
  - *Construction.* Noise tests whose rejection probability is `O(noise)` give
    `gamma = O(eta)`, which is sub-sqrt.
  - *Where it dies.* At the soundness certification step, by
    `black-box-repetition-needs-sqrt-scale-soundness-gap`.
  - *What would survive.* An analysis that uses instance structure, such as
    expansion, for soundness.
* **Expansion-certified repetition (2026-09-18, swarm-0917, `w10-ugc-last1`).**
  This attacks the survivor that the previous attempt left open.
  - *Construction.* Take sub-sqrt NP-hard sources whose NO hosts have walk gap
    `λ`. Repeat them `n` times, and certify soundness by an expansion-dependent
    rate. AKKSTV Theorem 4.3 is the example: rate `Ω(λγ/log(1/γ))`
    (`akkstv-expansion-parallel-repetition-bound`).
  - *Where it dies.* At the soundness certification step, by
    `expansion-certified-repetition-caps-deficit-ratio` (ESTABLISHED). The
    `r = 1` spectral-gap SDP test of `spectral-gap-no-outputs-cannot-prove-ugc`
    runs on the NO sources. Unless `P = NP`, it forces `λγ <= 1592 η`.
    - Any certified rate `ψ <= Kγ^2 + κλγ` then gives output deficit ratio
      `<= 2Kγ^2/η + 3184κ`.
    - Pure expansion rates are therefore capped at a constant.
    - Mixed rates need a sqrt-scale source, which is circular.
    - Certificates through any polynomial-time multiplicative value bound,
      such as the Feige–Lovász `σ`, certify an empty gap.
  - *What would survive.* This is the decomposition. The route needs (P1)
    hardness of a λ-gapped source, together with (P2) a repetition rate on
    λ-gapped unique games that is superlinear in `λγ` and superquadratic in
    `γ`, for example `sqrt(λ)·γ` when `γ^2 << λ`. Soundness analyses that use
    more than `(λ, γ)` also survive.
  - *Unchecked.* Raz–Rosen (CCC 2012) proves strong repetition for projection
    games on expanders. It is killed here if its `c(λ)` is `O(λ)`, and it is a
    (P2) candidate otherwise. Its exact form was not verified.
  - *Related failed attempt.* Moshkovitz, arXiv 2103.08743, amplified UG on
    small-set expanders, and the paper is withdrawn. The stated reason is "SSE
    requires simulation conditioned on falling into the small set, which is not
    necessarily possible."
