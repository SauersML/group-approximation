---
rg: 2
id: thompson-f-ramsey-amplification-needs-unbounded-tower-overhead
kind: claim
title: In Thompson's F, amplifying 1/2-Ramsey balls to (1/u)-Ramsey balls costs more than any bounded number of exponentials over the Ramsey function
distinct_from:
  thompson-f-ramsey-function-iterates-reach-towers: that proves the transfer and the fork (Proposition D); this is the open branch of the fork on which an elementary Ramsey function can live, the negation of AMP.
  moore-ramsey-criterion-for-amenability: that imports the composition bound R̃(m, ε) ≤ R^p(m); this asks whether, in F, no fixed-height tower can replace that composition.
  thompson-f-is-amenable: that is the root; this claim implies it (see the route thompson-f-amenable-via-costly-ramsey-amplification) and is strictly stronger unless AMP fails in F.
---

**OPEN.** Notation is as in `moore-ramsey-criterion-for-amenability`, with `S = {x_0, x_1}`, `R = R_{F,S}`, `R̃ = R̃_{F,S}`
and `exp_D` the `D`-fold tower. Values may be `∞`, with `exp_D(∞) = ∞`.

**Statement (¬AMP).** For every integer `D ≥ 0` there are integers `m, u ≥ 1` with

`R̃(m, 1/u) > exp_D(R(exp_D(m+u)) + u)`.

For a fixed `D`, *AMP(D)* denotes the reverse inequality for all `m, u ≥ 1`, as in Proposition D of
`thompson-f-ramsey-function-iterates-reach-towers`. The claim is that AMP(D) fails for every `D`.

**It implies amenability of F.** A strict inequality forces the right side to be finite, so `R(exp_D(m_D+u_D)) < ∞`
for every `D`. Since `exp_D(m_D+u_D) ≥ exp_D(1)` is unbounded in `D`, and `R` is nondecreasing (monotonicity in `A`),
`R(M) < ∞` for every `M`. By Theorem 1.3 (2)⇒(4) of the imported criterion, `F` is amenable. If `F` is not amenable,
both sides are `∞`, AMP(D) holds trivially for every `D`, and this claim is false.

**Why it matters.** This is the independent prerequisite of Moore's "moderate rate" program.
- *Necessary for elementary Ramsey radii.* By Proposition D, if `R_F` is elementary then this claim holds. It is the
  only branch on which the elementary band of Proposition C can be inhabited.
- *If false* (AMP(D) holds for some `D`). Then either `F` is non-amenable or `R_F` is not elementary. The Ramsey
  reformulation is then pinned to the Følner tower like every other reformulation in the graph, and Moore's hope in
  Section 7 of *Amenability and Ramsey theory* dies.
- *If true.* `F` is amenable, and the composition depth in (3⇒4) of Moore's Theorem 2.1 is genuinely needed in `F`.
  An inductive construction of 1/2-Ramsey sets of elementary radius would then be a route that is not quantitatively
  as hard as building Følner sets directly.

**Known facts.**
- AMP(D) holds, with `D` depending on the group, in every amenable group whose function `F_{G,S}(m, ε)` is bounded
  by a fixed tower in `m + 1/ε`. The trivial chain `R̃ ≤ F_{G,S}` quoted in Moore's Section 3 gives it. So ¬AMP can
  only hold in groups with non-elementary Følner functions, and `F` is the finitely presented candidate.
- Naive majority amplification does not visibly give AMP. The idea is to take `u` 1/2-Ramsey witnesses and average
  their measures. But a witness is chosen after the coloring `E`, and the thresholds `E = {f ≥ t}` depend on the
  function being balanced. So the errors are not independent, and no `O(1/√u)` bound follows. This is heuristic,
  not an obstruction. It is why Moore's step (2⇒3) gets only `q = 3/4` per level. See Attempts.

## Attempts

- **2026-09-17 (swarm-0917-w6b-w6b-f-break, logic-computability).** Two attempts to decide AMP, both inconclusive.
  - *Amplification without composition (towards refuting this claim).* Use commuting rigid copies
    `F_{[0,1/2]} × F_{[1/2,1]} ⊆ F` to run independent 1/2-Ramsey trials in disjoint supports, then take product
    measures. It dies at the same point as the majority argument: the coloring `E` of the product ball is arbitrary,
    so it need not be a product coloring, and nothing forces the trials to be independent with respect to `E`.
  - *A model group where AMP fails.* There is no candidate yet. Such a group needs a non-elementary Følner function
    (Known facts). No Ramsey function of such a group has been computed in the literature this lane read.
- **2026-09-18 (swarm-0917-w8-w8-f-break, census computation).** This entry gives the first exact values of the
  Ramsey function of `F`, using a sharper unit-ball precision. It decides nothing about AMP. The node is
  `thompson-f-b1-ramsey-witnesses-are-at-most-one-third`, and its route certifies everything with DRAT-checked
  SAT and exact rational duals.
  - *Exact values.*
    - `R(1) = R(1, 1/2) = 3`, the same as in `F_2`.
    - `R(1, ε) = 7` for `1/3 ≤ ε < 1/2`.
    - `R(1, ε) ≥ 11` for `ε < 1/3`, since the profile `ρ_F(n)` is exactly `1/3` on radii 7 to 10.
    - The sharper precision costs `+4` radii from `1/2` to `1/3`. In `F_2` it never arrives, because
      `ρ_{F_2} ≡ 1/2`. This is the first point where `F` separates from the free group in Ramsey terms.
  - *Why this cannot decide AMP.* AMP compares `R̃(m, 1/u)` with the tower `exp_D(R(exp_D(m+u)) + u)`.
    - For `D ≥ 1` and every `m, u ≥ 1`, the bound `R(M) ≥ M` (criterion node) makes the right side at least
      `exp_D(exp_D(2) + 1)`. That is at least `2^5 = 32` when `exp_1(x) ≥ 2^x`.
      So the census values, which are small lower bounds on the left side, are consistent with AMP(D) and with ¬AMP.
    - `R` at the arguments AMP needs, such as `R(exp_D(2))`, is far out of computational reach. The census bears
    only on the qualitative question behind AMP: whether amplification in `F` is free-group-like.
  - *Function side (exact, item 5 of the node).* Take the extremal direction
    `w = (1/3)(x_0^{-1} − x_0) + (2/3)(x_1 − x_1^{-1})`.
    - An exactly checked `f : B_11 → [0,1]` has `Σ_a w_a f(ag) ≥ 0.3404` on `I_11`, so `R̃(1, 1/3) ≥ 12`.
    - The `{0,1}` version of the same direction dies at radius 11, and a DRAT-checked configuration of 71 elements
      is the obstruction. So along this direction, sets and functions (`R` versus `R̃`) separate in `F` by radius 11.
    - The floating LP optima of the relaxation in `F` agree with the exact `F_2` values
      `11/12, 15/16, 23/24, 31/32` for `n = 7..10`, and are about `47/48` at `n = 11`. So fractionally, `F` stays
      free-like in this direction.
  - *Belief update.* Neither branch gains support from the data. `F` looks free through radius 6. It then loses the
    ping-pong witness, and set witnesses are capped at `1/3`, while the fractional relaxation stays free-like
    through radius 11. The one structural lesson for AMP is that in `F` the obstruction to set witnesses appears
    well before the obstruction to function witnesses.
- **2026-09-18 (swarm-0917-w8-w8-f-follow, operator-algebras).** The hole is reduced to a set-versus-measure gap.
  It stays OPEN. The established parts are `coarse-ball-invariance-gives-fine-reiter-measures` and
  `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`.
  - *Precision amplification is free for measures.* Suppose one measure is moved by at most 1 in ℓ¹ by all of
    `B_{2K}`. Then `K−1` lazy-walk steps applied to its square root give a Reiter measure with error `O(K^{−1/2})`.
    The proof uses log-convexity of the even return moments. So `R̃(m, 1/u) ≤ F(m, 1/u) ≤ CR(exp_3(m+u)) + exp_3(m+u)`,
    where `CR` is the coarse Reiter radius. Consequently, if `CR(N) ≤ exp_E(R(exp_E N))` for all `N`, then AMP(E+3)
    holds and this claim is false. Every proof of ¬AMP must therefore show that `R_F` is non-elementarily below `CR_F`
    (RGAP₁). Majority, product-trial and nested-Ramsey amplification are all attacks on the wrong step.
  - *The converse direction is almost tight.* Towsner's Proposition 3.1 gives `CR(M) ≤ R̃(R̃(1, 1/4M), 1/4M)`.
    Hence AMP(D) bounds `CR` by a bounded tower around two compositions of `R`. So RGAP₂ implies this claim. That is
    the new route `thompson-f-costly-amplification-via-double-ramsey-reiter-gap`.
  - *Translation coding dies.* The idea was to code many colorings into one set `E` by far-apart translates
    `w_i ∈ B_M`, so that one Ramsey call balances all of them. It dies because the witness `ν` has support radius
    about `n ≥ M`. The regions `w_i·B_m·supp ν` then overlap, and the codes interfere.
  - *Where it dies.* The step from `∀E ∃ν` to `∃ν ∀E` at precision 1/2. A minimax over coarse `B_M`-invariance
    needs about `|B_M|` test functions, which means Towsner compositions of height about `5^M`. Nothing
    F-specific was found that either separates `R` from `CR` or collapses them.
