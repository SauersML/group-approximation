---
rg: 2
id: weakly-bernoulli-lift-iff-bernoulli-almost-lifts-proof
kind: route
title: Transfer lifted cocycle statistics along weak containment, and conversely take a weak-star limit of encoded almost-lifts
target: weakly-bernoulli-lift-iff-bernoulli-almost-lifts
requires:
  - treeable-free-actions-lift-across-finite-normal-extensions
---

Complete proof. Notation as in the claim: `1 -> N -> W -π-> Q -> 1`, `N` finite, `Q` countably infinite,
`B = (2^N)^Q` the Bernoulli shift with base the Cantor space `2^N` carrying the uniform product measure; it is
isomorphic to `[0,1]^Q`. The lifting criterion is Lemma 1 of
`treeable-free-actions-lift-across-finite-normal-extensions-proof`: a free p.m.p. `Q`-action lifts iff there is a
Borel `φ : Q × Y -> W` with `π(φ(q, y)) = q` and the cocycle identity a.e. We fix a set-theoretic section `σ` of `π`.

Weak containment (Kechris): `Y ≺ Z` iff for every finite Borel partition `{A_1, ..., A_k}` of `Y`, finite `F ⊂ Q`
and `δ > 0` there is a Borel partition `{B_1, ..., B_k}` of `Z` with `|μ(q A_i ∩ A_j) − μ(q B_i ∩ B_j)| < δ` for all
`q ∈ F`, `i`, `j`.

## (i) ⇒ (ii)

Let `Y ≺ B` be free and liftable, with lifted cocycle `φ_Y`. Fix a finite symmetric `F ∋ 1` and `ε > 0`. Let `P` be
the finite partition of `Y` by the tuple `(φ_Y(q, y))_(q ∈ F)`; its cells are indexed by tuples
`t = (t_q)_(q ∈ F)` with `t_q ∈ π^-1(q)`, so there are at most `k = |N|^|F|` cells. For `q_1, q_2, q_1 q_2 ∈ F` the
defect set `D_Y(q_1, q_2) = {y : φ_Y(q_1 q_2, y) ≠ φ_Y(q_1, q_2 y) φ_Y(q_2, y)}` is the union of the sets
`A_t ∩ q_2^-1 A_s` over the pairs `(t, s)` with `t_(q_1 q_2) ≠ s_(q_1) t_(q_2)`, and it is null.

Take a partition `{B_t}` of `B` as in the definition, with `F` and `δ = ε / k^2`. Put `φ(q, x) = t_q` for `x ∈ B_t`.
Then `π(φ(q, x)) = q`, and the defect set `D(q_1, q_2)` is the union of the sets `B_t ∩ q_2^-1 B_s` over the same
pairs. Since `μ(B_t ∩ q_2^-1 B_s) = μ(q_2 B_t ∩ B_s)` and the corresponding sets in `Y` are null,
`μ(D(q_1, q_2)) < k^2 δ = ε`.

## (ii) ⇒ (i)

Choose finite sets `F_1 ⊂ F_2 ⊂ ...` exhausting `Q` and `ε_m -> 0`, and almost-lifts `φ_m` on `F_m × B` as in
(ii). Extend each by `φ_m(q, x) = σ(q)` for `q ∉ F_m`.

*Encoding.* Let `K = (2^N)^Q × Π_(q ∈ Q) (π^-1(q))^Q`, a compact metrizable, totally disconnected space. `Q` acts by
shifting the inner index: `(h·x)_0(g) = x_0(h^-1 g)` on the first factor and `(h·x)(q)(g) = x(q)(h^-1 g)` on the
others. Define `E_m : B -> K` by `E_m(b) = (b, (g -> φ_m(q, g^-1 b))_(q ∈ Q))`. Then
`E_m(h b)(q)(g) = φ_m(q, g^-1 h b) = E_m(b)(q)(h^-1 g)`, so `E_m` is equivariant and `ν_m = (E_m)_* μ` is
`Q`-invariant. The first marginal of `ν_m` is the Bernoulli measure.

*Limit.* Pass to a weak-star convergent subsequence `ν_m -> ν`. The measure `ν` is `Q`-invariant, and its first
marginal is still the Bernoulli measure. So `(K, ν)` has `B` as a factor and is free.

*Exact lift in the limit.* For `q_1, q_2 ∈ Q`, the set
`D = {x ∈ K : x(q_1 q_2)(1) ≠ x(q_1)(q_2^-1) · x(q_2)(1)}` is clopen, since it depends on three coordinates with
finitely many values. `E_m^-1(D)` is the defect set of `φ_m` at `(q_1, q_2)`, because
`φ_m(q_1, q_2 b) = E_m(b)(q_1)(q_2^-1)`. So `ν_m(D) < ε_m` once `q_1, q_2, q_1 q_2 ∈ F_m`. Since `1_D` is continuous,
`ν(D) = lim ν_m(D) = 0`. Put `φ(q, x) = x(q)(1)`. Then `π(φ(q, x)) = q`, `φ(q_1, q_2 x) = x(q_1)(q_2^-1)`, and the
cocycle identity holds `ν`-a.e. By the lifting criterion `(K, ν)` is liftable.

*Weak containment.* Clopen sets form a countable algebra that generates the Borel sets of `K`, so it is dense in
the measure algebra of `ν`. Every finite Borel partition of `(K, ν)` can be approximated in measure by a clopen
partition, which changes the statistics `ν(q A_i ∩ A_j)` by an arbitrarily small amount. For a clopen partition,
`ν(q A_i ∩ A_j) = lim ν_m(q A_i ∩ A_j)`, and `ν_m(q A_i ∩ A_j) = μ(q E_m^-1 A_i ∩ E_m^-1 A_j)` is realised exactly by
the partition `{E_m^-1 A_i}` of `B`. So `(K, ν) ≺ B`. Take `Y = (K, ν)`. ∎

## The addenda in the claim

- **Other free actions.** If `(ii)` holds on `B`, it holds on every free p.m.p. action `Z`: `B ≺ Z` by
  `abert-weiss-free-actions-weakly-contain-bernoulli`, and the argument of (i) ⇒ (ii) transfers the finitely many
  partition statistics that define `φ` and its defect sets from `B` to `Z`.
- **Weak equivalence.** A free `Y ≺ B` is weakly equivalent to `B`, by the same import.
