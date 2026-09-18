---
rg: 2
id: finitely-generated-field-crossed-products-have-rank-condition
kind: claim
title: Every skew group ring of any group over a finitely generated field has the rank condition, and is stably finite when the action is faithful
distinct_from:
  rational-function-field-crossed-products-have-the-rank-condition: that covers only purely transcendental k(x_1..x_n) and counts points with Schwartz–Zippel; this covers every finitely generated field (function fields of K3 surfaces, Calabi–Yau varieties, number fields, any variety) and counts points with Lang–Weil after reducing a spread-out model modulo a prime chosen away from the minimal primes of one element.
  field-crossed-product-rank-condition-survival-cases: that needs an amenable quotient, algebraic coefficients, or an invariant measure on complex points; this needs no hypothesis on the group or the action.
  virtually-hughes-free-field-crossed-products-are-stably-finite: that restricts the group and allows any field and cocycle; this allows any group and restricts to finitely generated fields with trivial cocycle.
---

**ESTABLISHED (unreviewed)** by [[finitely-generated-field-crossed-products-rank-condition-proof]].

Let `K` be a field that is finitely generated as a field over its prime field `k`. Let `G` be any group, and let
`σ: G -> Aut(K)` be any action. Write `K ⋊ G` for the skew group ring with trivial cocycle.

**Theorem 1 (rank condition).** If `A ∈ M_{d×r}(K ⋊ G)`, `B ∈ M_{r×d}(K ⋊ G)` and `AB = I_d`, then `r >= d`.

**Theorem 2 (stable finiteness).** If `σ` is faithful, then `AB = I_d` implies `BA = I_d` in `M_d(K ⋊ G)`.

**Local form.** Theorems 1 and 2 hold for `K' ⋊ G`, with `K'` any field and `σ: G -> Aut(K')`, if the following
holds: for every finite `E ⊂ K'` and finite `T ⊂ G` there is a finitely generated subfield `K_0 ⊇ E` with
`σ_g(K_0) ⊆ K_0` for all `g ∈ T`. For Theorem 2, `σ` must be faithful on `K'`.

**Mechanism.** Spread `K` out to a finitely generated domain `R`, reduce modulo a prime `p` chosen so that one
fixed nonzero `D ∈ R` lies in no minimal prime of `R/pR`, and let `G` act by partial substitutions on
`Ω = Hom(R, F_q)`. The model is exact off `V(D)`, which has lower dimension. Lang–Weil gives
`|V(D)(F_q)| / |Ω| = O(q^{-1})` along `q = p^{aj}`.

**Consequences.**
- **Witness class 3 of `some-field-crossed-product-fails-the-rank-condition` dies.** No untwisted skew group ring
  over a finitely generated field is a witness. This includes automorphisms of K3 or Calabi–Yau function fields,
  `Bir(V)` for any variety `V` over `Q` or `F_p`, and number fields.
- **What a witness still needs.** Either (1) a cocycle that is not a coboundary on finite models, or (2) a field
  that is not locally stable: some finite data lie in no finitely generated subfield stable under finitely many
  `σ_g`. Bernoulli fields `F_p(x_g : g ∈ G)` are the basic case of (2).
- **Kaplansky specialisation.** `k[G] ⊆ K ⋊ G` as the span of the `u_g`. So Theorem 2 gives direct finiteness of
  `k[G]` for every `G` acting faithfully on a finitely generated field of characteristic `p`.
