---
rg: 2
id: coordinate-action-not-sofic-proof
kind: route
title: Soficity of the coordinate action would make W sofic
target: coordinate-action-not-sofic
requires:
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Soficity of the coordinate action would make W sofic

A two-line contradiction between two theorems that were both read verbatim in
their authors' own source on 2026-08-14. `requires: []` is a proof commitment.

## Inputs, verbatim

Gao–Kunnawalkam Elayavalli–Patchell, *Soficity for group actions on sets and
applications*, arXiv:2401.04945 (*Res. Math. Sci.* 2025), Theorem A = 3.6:

> Let G, H be sofic groups, α: H ↷ X be a sofic action. Then the generalized
> wreath product G ≀_α H is sofic.

Kun–Thom, arXiv:2608.06222v1, Theorem A:

> Let Γ be an infranormal but not normal subgroup of G, and suppose that both
> Γ and G have Kazhdan's property (T). Then (ℤ/2ℤ)≀_{G/Γ}G is not sofic.

## Proof

Write `Γ ≤ G` for the pinned Theorem E pair and `α : G ↷ G/Γ` for the coset
action. Suppose `α` were a sofic action.

The acting group `G` is residually finite (Kun–Thom Theorem E), hence LEF,
hence sofic — both implications are kernel-checked here, as
`Sofic/LEFSofic.isSofic_of_isLEF` and the residually-finite-implies-LEF step in
the same file. The lamp group `ℤ/2ℤ` is finite, hence sofic
(`Sofic/SoficPositiveControl.isSofic_of_finite`).

GKP Theorem A, applied with their `G := ℤ/2ℤ`, their `H := G`, their `X := G/Γ`
and their `α := α`, then yields that the generalized wreath product
`(ℤ/2ℤ) ≀_α G = (⊕_{G/Γ} ℤ/2ℤ) ⋊ G = W` is sofic.

That is exactly the group Kun–Thom Theorem A proves is not sofic, at exactly
the pair Theorem E certifies. Contradiction. Hence `α` is not a sofic action. □

## The independent second route to the same conclusion

Kun–Thom Corollary D states it directly for the measure-theoretic form, with no
appeal to GKP:

> Under the assumptions of Theorem C, suppose in addition that Γ is not normal
> in G. If (K,κ) is a nontrivial standard probability space, then the
> generalized Bernoulli action G↷(K,κ)^{G/Γ} is not sofic.

Here "sofic" is Păunescu's Definition 1.4 — verbatim, an embedding
`L^∞(X)⋊_α G ↪ Π_{k→ω}M_{n_k}(ℂ)` with `L^∞(X) ⊂ Π_{k→ω}D_{n_k}(ℂ)` and
`G ⊂ Π_{k→ω}P_{n_k}(ℂ)`, `P_{n_k}` the **permutation** matrices. So Corollary D
says precisely: no trace-preserving embedding of `M_KT = L^∞({±1}^{G/Γ}) ⋊ G`
has the lamp algebra diagonal and the group unitaries permutations.

The two routes are not redundant. The first kills the combinatorial hypothesis
that the set-level permanence theorems consume; the second kills the
embedding-level hypothesis directly, and is what makes "non-Cartan" the exact
residual requirement on any hyperlinear model.

## Scope

Nothing here says `M_KT` is not Connes-embeddable, and nothing here says `W` is
not hyperlinear. Corollary D constrains the *shape* of an embedding, not its
existence. Confusing the two would close `hyperlinear-wreath-model` by
sleight of hand; it remains open.
