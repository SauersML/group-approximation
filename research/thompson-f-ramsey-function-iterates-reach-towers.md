---
rg: 2
id: thompson-f-ramsey-function-iterates-reach-towers
kind: claim
title: If Thompson's F is amenable, a linear number of iterates of its Ramsey function reaches a tower, so no quasi-polynomial ladder bounds it, but the transfer is silent on elementary Ramsey functions unless Ramsey sets amplify cheaply
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that bounds the size of Følner sets; this transfers it to Moore's Ramsey function. The Ramsey function only has to reach a tower after O(n) iterations, so it may be one full exponential level lower.
  f-dyadic-confinement-witness-times-match-folner-function: that shows confinement witness times are the Følner function up to one exponential; this shows the Ramsey function is the one reformulation in the graph whose known transfer loses a whole iteration level, not a single exponential.
  thompson-f-cardinality-certificates-need-tower-degree: that bounds the degree of cardinality certificates on the amenable side; this bounds the growth rate of ball radii that are 1/2-Ramsey.
  moore-ramsey-criterion-for-amenability: that is the imported criterion and Towsner's inequality; this is their quantitative consequence for F.
---

**ESTABLISHED** by `thompson-f-ramsey-function-iterates-reach-towers-proof`. It is a direct proof from two
imports, `moore-ramsey-criterion-for-amenability` and `thompson-f-folner-function-exceeds-every-tower`.
It has not been independently reviewed, and no priority is claimed.

**Setting.**
- `S = {x_0, x_1}` and `Γ = S ∪ S⁻¹`. `C > 1` is Moore's tower constant for `Γ`.
- `R = R_{F,S}` is the Ramsey function: `R(m)` is the least `n` such that `B_n` is 1/2-Ramsey with respect to `B_m`.
- `R̃ = R̃_{F,S}` is as in Moore's Section 3.
- `exp_0(x) = x`, `exp_{q+1}(x) = 2^{exp_q(x)}`, and `log_q` is the `q`-fold `log₂`.
- For `n ≥ 1`, put `k_n = ⌊2Cⁿ⌋ + 1`, let `p_n` be the least `p` with `(4/3)^p > 4k_n`, and put `j_n = 2p_n`. Then
  `2n·ln C/ln(4/3) < j_n ≤ 2n·ln C/ln(4/3) + 2 ln 12/ln(4/3) + 2`.

Assume `F` is amenable, so that `R(m) < ∞` for every `m`.

**Theorem A (iterates reach towers).** For every `n ≥ 1` and every `j ≥ j_n`,
`R^j(1) ≥ exp_{n−1}(0)/log₂5`.

**Corollary B (the quasi-polynomial ladder is dead).** There are no `q ≥ 0`, `d ≥ 1` and `M` with
`log_q M ≥ 2` such that `R(m) ≤ exp_q((log_q m)^d)` for all `m ≥ M`. So no polynomial bound
(`q = 0`), no quasi-polynomial bound (`q = 1`), and no bound `exp_q(poly(log_q m))` holds for the ball
radius of 1/2-Ramsey sets of `F`.

**Proposition C (the inference cannot see elementary functions).** Let `r ≥ ln(4/3)/(2 ln C)` be an
integer and put `Q = exp_r`. Consider any `k, p` with `(3/4)^p < 1/(4k)`, and any `n` with `2Cⁿ < k`. Then
`5^{Q^{2p}(1)} ≥ exp_n(0)`. So the elementary function `Q` satisfies every instance of Theorem 3.2 that
Moore's tower bound constrains. Theorem 3.2 and the tower bound alone cannot exclude an elementary Ramsey
function for `F`, although `Føl_{F,Γ}` is not eventually dominated by any `exp_p`.

**Proposition D (the fork).** Call the following *AMP(D)*: for all integers `m ≥ 1` and `u ≥ 1`,
`R̃(m, 1/u) ≤ exp_D(R(exp_D(m+u)) + u)`.
If AMP(D) holds for some `D`, then for every `q` there is an `m` with `R(m) > exp_q(m)`. In particular
`R` is not elementary.

**Why it matters.**
- *Moore's hope is split into two prerequisites that can fail independently.* In his Section 7 he hoped
  that 1/2-Ramsey sets for `F` "might grow at a more moderate rate". Corollary B kills every moderate rate
  on the quasi-polynomial ladder. Proposition C shows the known transfer leaves the elementary band open.
  Proposition D shows that this band survives only if Ramsey sets in `F` do *not* amplify with
  bounded-tower overhead. That is the open claim `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`
  (¬AMP). It implies the root through the route `thompson-f-amenable-via-costly-ramsey-amplification`.
- *Where the tower is lost.* The dying step is the downward recursion (3⇒4) of Moore's Theorem 2.1.
  Precision `q^n` is bought by `n` nested Ramsey sets `B_{i+1}` for `B_i`, so `R` is composed
  `Θ(log 1/ε)` times. With `ε ≈ C^{−n}` that is `Θ(n)` compositions, which is exactly the tower height
  in Moore's bound. Any Ramsey-to-Følner transfer that amplifies through nested Ramsey sets pays this cost.
  So no such transfer can give more than Theorem A. The invariant is `log*` of the iterate, `log* R^j(1)`,
  and it grows linearly in `j`.
- *Contrast with the rest of the graph.* Every other reformulation of the root recorded so far is pinned
  to the Følner tower up to one exponential. That includes extensive-amenability witnesses, confinement
  witness times and cardinality certificates. The Ramsey function is the only one whose known lower bound
  leaves a full level of the Grzegorczyk hierarchy open.
