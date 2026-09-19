---
rg: 2
id: thompson-f-guba-q4-systems-have-common-multiples
kind: claim
title: Guba's systems Q_4 have nonzero solutions over every field, and {x_0, x_1}-density above 4 - 2/k solves every Q_k
distinct_from:
  thompson-f-rescaled-x0-binomials-have-common-multiples: that settles Q_k over F_2 and when at most one form is a full trinomial; this settles Q_4 (and so Q_1 to Q_4) for all coefficients over every field, including two or more full trinomials, and it names the density threshold that settles each Q_k.
  thompson-f-support-three-pairs-have-common-multiples: that handles pairs with joint support at most three, and records that it does not touch Q_4; this handles systems of five linear forms with a dimension count fed by a set Y with |AY| < (5/4)|Y|.
  thompson-f-evacuation-schemes-need-capacity-three: that uses the same density theorem to exclude capacity-two evacuation schemes; this converts the density theorem into a small-tripling set for {x_0, x_1, x_2} and solves the linear systems Q_4.
  thompson-f-is-not-amenable: that is the root; this removes the smallest named group-ring candidate for a negative answer (Guba's Q_4) and decides nothing about the root.
  thompson-f-is-amenable: that is the root; this settles one finite family of Ore-type systems and decides nothing about the root.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that reduces non-amenability to doubling of a monomial set; this shows that the tripling ratio of A = {x_0, x_1, x_2} is below 5/4.
artifacts:
  - experiments/guba-qk-2026-09-17/qk_linalg.py
---

**ESTABLISHED** through `thompson-f-guba-q4-systems-have-common-multiples-proof` (not independently
reviewed; the only import beyond graph nodes is Guba's density theorem, quoted verbatim in the route).

Let `K` be any field, `M` the positive monoid of Thompson's group `F`, `A = {x_0, x_1, x_2}`. For
finite `Z ⊂ F` let `δ(Z)` be the average induced degree of `Z` in the Cayley graph of `F` with
respect to `{x_0^±1, x_1^±1}`, and `δ̄ = sup_Z δ(Z)` (Guba's density; `δ̄ = 4` iff `F` is amenable).

1. **Tripling bound.** For every finite nonempty `Z ⊂ F`,
   `|{1, x_0, x_1} Z| <= (3 - δ(Z)/2) |Z|`. The set `Y = x_0^-1 ψ(Z)` has `|Y| = |Z|` and
   `|A Y| = |{1, x_0, x_1} Z|`. Here `ψ : F -> F`, `x_0 -> x_2 x_0^-1`, `x_1 -> x_1 x_0^-1`, is the
   embedding of `thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f`. So
   `inf_Y |AY|/|Y| <= 3 - δ̄/2`.
2. **Q_k from density.** Let `k >= 1`. If `δ̄ > 4 - 2/k`, then Guba's Problem `Q_k` has a positive
   solution for all coefficients over every field. That is, for any nonzero
   `t_i = α_i x_0 + β_i x_1 + γ_i x_2` (`0 <= i <= k`), there are `u_0, ..., u_k ∈ K[M]`, all
   nonzero, with `t_0 u_0 = t_1 u_1 = ... = t_k u_k`.
3. **Q_4.** Guba's theorem `δ̄ > 3.5` (survey arXiv:2305.07113, Theorem 2.7; from arXiv:2210.12304)
   gives `δ̄ > 4 - 2/4`. So every system `Q_4`, over every field and for all coefficients, has a
   solution with all `u_i` nonzero. Hence also every `Q_k` with `k <= 4`.
   There are finite `Y ⊂ M` with `|AY| < (5/4)|Y|`.

**Belief changed.** The survey says: "The case k = 4 looks as a possible candidiate to a negative
solution (that is, all solutions are zero). If true, this will imply that the constant ε = 1/4 fits
into the above condition." That candidate is dead. The same survey proves the density theorem
(its Theorem 2.7) that kills it, but does not connect the two. The graph listed `Q_4` over fields
other than `F_2` as an open candidate in `thompson-f-is-not-amenable`,
`thompson-f-rescaled-x0-binomials-have-common-multiples` (item 5) and
`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md`. Those entries are superseded.

**Precise obstruction for the Q-family.** A negative instance of `Q_k` would force `δ̄ <= 4 - 2/k`,
that is, Cheeger constant `ι*(F; {x_0, x_1}) >= 2/k`. So:
- `Q_k` is not a non-amenability certificate for any `k <= 4`;
- the smallest open member is `Q_5`, and it falls to any finite `Z` with `δ(Z) > 3.6`, only
  `0.0996` above Guba's `3.5004`;
- every future density improvement kills a further block of the family. A density sequence tending
  to 4 (amenability) solves all `Q_k`.

**Calibration.** Belk–Brown sets have density tending to `3.5`. By item 1 they give ratios
`|AY|/|Y|` tending to `5/4` from above, which is under `4/3`. That recovers Guba's Theorem 3.12
(`|AS| < (4/3)|S|`, hence `Q_3`). It misses `Q_4` only at the boundary, so the strict inequality in
Guba's density theorem is exactly what `Q_4` needs.

**Computation (context, not used in the proof).** `experiments/guba-qk-2026-09-17/qk_linalg.py`
searches exactly, mod `p = 1000003`, for solutions with `u_i` homogeneous of degree `n` and letters
`<= L` in `M`, using random generic forms. Results:
- `Q_1` first appears at `n = 2`: kernel dimensions `0, 1, 7, 35, 155` for `n = 1..5` at `L = n + 2`,
  verified by direct multiplication.
- `Q_2`, `Q_3`, `Q_4` have no solutions for `n <= 5`.
- So `Q_4` solutions are not low-degree. The existence proof gives supports inside the sets
  inherited from Guba's construction, of size about `2^27200` by the survey's estimate. It gives no
  explicit degree bound.

**Scope.** Novelty is not claimed for the density theorem. The contribution is the reduction in items
1–2 and the consequence for Guba's candidate. Nothing about the root is decided.

Proof route: `thompson-f-guba-q4-systems-have-common-multiples-proof`.
