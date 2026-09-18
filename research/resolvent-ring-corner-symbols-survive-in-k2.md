---
rg: 2
id: resolvent-ring-corner-symbols-survive-in-k2
kind: claim
title: The corner map Z_(l) -> e R_l e induces an injection K_2(Z_(l)) -> K_2(R_l), so the corner tame symbols of R_l generate an infinitely generated subgroup
distinct_from:
  resolvent-ring-has-path-normal-form: that is the additive and multiplicative structure of R_l; this is a K_2 consequence read off from it, through the quotient killing all paths with a middle letter.
  infinitely-generated-symbols-block-fp-elementary-groups: that is the general lemma turning infinitely generated symbols into non-finite-presentation; this supplies the infinitely generated symbols for R_l.
artifacts:
  - research/artifacts/gq-gq-k2-q-resolvent-corner.md
  - research/artifacts/gq-referee-b-resolvent-ring-corner-symbols-survive-in-k2.md
---

**ESTABLISHED (2026-09-18)** through `resolvent-ring-corner-symbols-survive-in-k2-proof`. Lane proof (gq-k2-q).
*Reviewed (gq-referee-b, citation and hypothesis lens):* PASS, with one wording fix (W1, applied):
`research/artifacts/gq-referee-b-resolvent-ring-corner-symbols-survive-in-k2.md`. Inputs:
- the refereed `resolvent-ring-has-path-normal-form`;
- Suslin's excision theorem, as quoted from Tamme in `harmonic-coefficient-rings-are-k-equivalent-to-lc-proof`;
- textbook facts: Morita invariance and colimits for `K_2` of matrix rings, and the tame symbol.

## Statement

Let `l` be a prime and `R_l` the ring of `resolvent-presentation-ring-is-residually-finite`, with corner
homomorphism `θ : Z_(l) -> e R_l e`.

1. **A detecting quotient.** The span `J` of the path elements `[a|K|b]` with `K` nonempty is a two-sided ideal. In
   `R_l / J = D ⊕ M`:
   - `M ≅ M_Z^fin(Z_(l))` is the ring of finitely supported `Z × Z` matrices over `Z_(l)`, via
     `[a||b] ↦ E_(a,−b)`;
   - `θ(c) ↦ c E_(0,0)`.
2. **Injectivity.** `K_2(R_l/J) ≅ K_2(D) ⊕ K_2(Z_(l))`, and the composite
   `K_2(Z_(l)) -> K_2(R_l) -> K_2(R_l/J)` is the inclusion of the second summand. Hence
   `θ_* : K_2(Z_(l)) -> K_2(R_l)` is injective.
3. **Corner symbols.** For `λ, μ ∈ Z_(l)^x` and `N >= 3`, let `c(λ,μ) ∈ K_2(N, R_l)` be the image of the Steinberg
   symbol `{λ,μ}_N ∈ St_N(Z_(l))` under `St_N(θ)`.
   - The stable classes of the `c(λ,μ)` generate a subgroup of `K_2(R_l)` isomorphic to the symbol subgroup of
     `K_2(Z_(l))`.
   - That subgroup is not finitely generated. Its image in `K_2(Q)` has a nonzero tame symbol `∂_q` for every odd prime
     `q ≠ l` (`∂_2` is trivial, since `F_2^x = 1`), from `{q, g_q}` with `g_q` a primitive root modulo `q`, and a finitely generated torsion group has
     only finitely many nonzero components.

This answers the crux of `resolvent-steinberg-rf-residual-is-finitely-normally-generated`: the corner tame symbols
do survive, independently, in `St_N(R_l)`.
