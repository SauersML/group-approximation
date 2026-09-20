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
* **Repetition of any bounded-alphabet base, any soundness argument (2026-09-19,
  swarm-0917, `w17-ugc-last1`).** This attacks the (P2) survivor of the
  previous attempt from the completeness side.
  - *Construction.* Any route "NP-hard base family `G_x` of alphabet `k`, then
    `G_x ↦ G_x^l`", with `l` of polynomial bit size and soundness argued by
    anything (universal, expansion, SSE, threshold rank, or nothing).
  - *Where it dies.* At the soundness of the output, by
    `parallel-repetition-cannot-substitute-rounds-for-alphabet` (ESTABLISHED,
    from the imported Steurer rounding
    `steurer-parallel-repeated-unique-games-rounding`). The invariant is the
    base SDP deficit. The base SDP, solved on `G_x` and never on `G_x^l`,
    decides every repeated gap of ratio `C_out > 2 C_1 sqrt(ln k)`, for every
    `l`. So unless `P = NP`, repetition reaches ratio `C` only if
    `ln k >= C^2/(4C_1^2)`, and UGC at `eps` only if
    `ln k >= 1/(16 C_1^2 eps)`. Rounds never pay for base alphabet.
  - *Decomposition of (P2).* It splits into (R1) an NP-hard λ-gapped base at
    alphabet `ln k >= C^2/(4C_1^2)`, and (R2) a per-round rate `ψ` valid on all
    its NO instances, SDP-fooling ones included, in the window
    `0.79 C <= ψ/η <= 7.51 C_1^2 ln k`. Each can fail on its own.
  - *Raz–Rosen, re-checked.* The previous attempt's "Unchecked" item. Search
    snippets (the PDF was unreachable) give, for projection games on graphs of
    spectral gap `λ`, a strong bound `(1 − γ)^Ω(c(λ) n)` with `c(λ) = poly(λ)`.
    That is a rate `a c(λ) γ`, linear in `γ`. If `c` is read literally as a
    polynomial, it is killed by the existing node:
    - the odd cycle `C_m` is a projection game with `γ = 1/2m` and gap
      `λ_m = Θ(1/m^2) > 0`;
    - `raz-odd-cycle-repetition-lower-bound` at `n = ⌊m^2/16B^2⌋` gives
      `val >= 3/4`, which forces `c(λ_m) <= 32 B^2 ln(4/3)/(a m) → 0`;
    - so `c(0) = 0`, and on `[0,1]`, `c(λ) <= ||c||_1 λ`;
    - the rate therefore has the shape `κλγ`, with ratio capped at `3184 κ` by
      `expansion-certified-repetition-caps-deficit-ratio`.

    Under a non-polynomial reading, the argument only gives `c = o(1)` at `0`.
    In either reading, bounded-alphabet Raz–Rosen routes are killed by the new
    node.
  - *What would survive.* Heterogeneous products `G_1 × ... × G_l` ((S1) is
    imported only for `G^l`); derandomized, partial or fortified repetition;
    repetition followed by alphabet reduction or composition; and bases whose
    alphabet already has `ln k >= C^2/(4C_1^2)`, which is (R1).
* **Raz–Rosen expander repetition, checked against the verbatim proof
  (2026-09-19, swarm-0917, `w17-ugc-pull`, calibration).** **Dead.** This
  resolves the "Unchecked" item above.
  - *Source.* The ECCC TR10-142 PDF was obtained. The quotations are in
    `raz-rosen-expander-projection-repetition-citation`.
  - *What the proof certifies.* By `raz-rosen-expander-repetition-rate-is-quartic-in-gap`
    (ESTABLISHED), the proof of Theorem 2 first amplifies to deficit
    `10^(−15) λ` in `m = 10^10 log(2/λ)/(ελ^2)` rounds, then applies Rao. The
    certified per-round rate is `ψ <= 2c · 10^(−40) ε λ^4/log(2/λ)`, where `c`
    is Rao's constant and `c <= 6`.
  - *Class membership.* That rate lies in `Rate(0, 2c · 10^(−40))`. So
    `expansion-certified-repetition-caps-deficit-ratio` item 3 caps the ratio
    at `R < 4 · 10^(−36)`, unless `P = NP`. Theorem 1 (general games) lies in
    `Rate(10^(−12)/16, 0)`, and item 4 makes that route circular.
  - *Why the proof reading matters.* The statement-level odd-cycle reading
    needs `C_m` to count as uniform over the edges of a biregular graph. That
    holds only as a multigraph, and the naive simple splitting has value 1.
  - *Invariant and step.* The invariant is `ψ/η`, and the route dies at
    soundness certification.
  - *Survivor.* Unchanged: (P2) needs a rate superlinear in `λγ`. No published
    expander bound on record (AKKSTV, Raz–Rosen) has one.
* **Set-indexed (unordered) repetition** (2026-09-20, swarm-0917, w21,
  `swarm-0917-w21-w21-ugc-last1`). The hole stays OPEN. The new node is
  `set-indexed-repetition-escapes-the-base-sdp-bound`, which is ESTABLISHED.
  - *Construction.* Repeat `n` times but hand each player an unordered set of
    questions, `G^{{n}}`, so that the coordinate matching is hidden.
  - *Result (A).* On the tagged odd cycle `G_{m,M}` with `M >= n^2`, the
    set-indexed value is at most
    `2[2m/n + 2m e^{-n/(8m)} + 6(3/4)^{n/(2m)}]`. At `n = m^{3/2}` this is
    `O(m^{-1/2})`, while `n (1 - sdp) -> 0` and the ordered value tends to 1.
    So (S1) and the rounds-versus-alphabet kill do not apply to set-indexed
    amplifiers.
  - *Mechanism.* Tag anonymity: exchangeable Bob tags cost `1/C(n_z, r_z)` at
    every mixed position, and the odd cycle forces a mixed position.
  - *Where it dies (B).* A universal set bound still dies. On disjoint copies
    of `C_m` the copy index is a public order, so Raz's strategy runs and
    `F_set(gamma, n) >= 1 - 4 B gamma sqrt(n)`. The sqrt-scale kill therefore
    transfers verbatim.
  - *Survivor.* An anonymity-certified set repetition: a tagged-set soundness
    bound for the reduction's own tagged instances at `n ~ eps'/eta` and
    `gamma = o(sqrt eta)`. This is the first independently failable
    prerequisite.
