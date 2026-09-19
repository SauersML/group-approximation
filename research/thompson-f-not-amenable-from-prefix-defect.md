---
rg: 2
id: thompson-f-not-amenable-from-prefix-defect
kind: route
title: A prefix observation with positive shadow defect gives a flow rule with inflow bounded below outflow, hence a doubling monomial set and non-amenability
target: thompson-f-is-not-amenable
requires:
  - thompson-f-prefix-observation-shadow-defect
  - thompson-f-flow-certificate-observation-gate
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
---

Notation as in `thompson-f-flow-certificate-observation-gate`: `M` is the positive monoid of `F`,
identified with forests; `π_K(y) = (t_0, ..., t_(K−1))` with `K = I(S) + D_S + 1`.

Assume `thompson-f-prefix-observation-shadow-defect`: there are a finite `S ⊆ M` and `λ > 1` with
`δ_λ(π_K) > 0`.

1. By **Theorem A** of `thompson-f-flow-certificate-observation-gate` (the gate is exact), applied to
   `Ψ = π_K` and that `λ`, there is a rule `G : S × X_K → [0, ∞)` reading `π_K` with
   `sup_z in_G(z) < ∞` and `inf_y out_G(y) > λ · sup_z in_G(z)`. Write `c = sup_z in_G(z)`; the proof of
   Theorem A shows `c > 0`.

2. Put `w(s, y) = G(s, π_K(y)) / c`. Then `Σ_(s: split_s z defined) w(s, split_s z) <= 1` for every `z`,
   and `Σ_(s ∈ S) w(s, y) > λ` for every `y`. So `w` is a certificate for `S` with ratio `λ > 1` in the
   sense of Section 2 of `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`.

3. By **Lemma 2.1(a)** of that file, a certificate with `λ > 1` makes some finite `S^k ⊆ M` doubling,
   and by item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles` no finite subset of `M` is
   doubling when `F` is amenable. Hence `F` is not amenable. ∎

*Nothing is lost by restricting to `π_K`.* The converse direction is Lemma A.4 of the gate: `π_K` is a
coarsening of `id_M`, so `δ_λ(π_K) <= δ_λ(id_M)`, and by Corollary A.3 a positive defect for `id_M` is
equivalent to non-amenability. Whether the two are equal is question 2 of
`thompson-f-prefix-observation-shadow-defect`; this route needs only the easy direction.
