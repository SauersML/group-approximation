---
rg: 2
id: rank-specialization-one-cell-asphericity-only-locally-indicable
kind: claim
title: If the L²-rank on Z[G] dominates a Sylvester rank function, the group killed by that rank function is locally indicable, so rank-specialization proofs of one-cell asphericity reach only Howie's class
distinct_from:
  locally-indicable-2-complex-with-h2-zero-is-aspherical: that is Howie's positive theorem for locally indicable fundamental groups; this shows that every rank-dominance route to the one-cell case already forces local indicability of the killed subgroup, so for trivial, abelian or locally indicable specializations it proves nothing beyond Howie.
  lo-amenable-limit-one-cell-complements-are-aspherical: that proves vanishing through a marked-group limit and an approximation theorem, where ranks agree only in the limit; this concerns a single comparison `rk_G ≥ rk'`, which is a different mechanism and is not obstructed here.
  whitehead-one-cell-counterexamples-have-positive-first-l2-betti: that says a non-aspherical one-cell complement has `b₁^(2) > 0`; this recasts `b₁^(2) = 0` as full von Neumann rank of one square Fox matrix with unimodular augmentation, and bounds what rank comparisons can prove it.
  non-ascending-one-cell-complements-have-vanishing-l2-b1: that is the open residual case of the vanishing statement; this is an obstruction for one family of methods, and says nothing about which groups are in the residual class.
---

**ESTABLISHED** through `rank-specialization-one-cell-obstruction-proof`.

## Setting

For a group `G` write `rk_G` for the von Neumann rank on matrices over `Z[G]`. For
`A ∈ M_{m×n}(Z[G])`, `rk_G(A)` is the `NG`-dimension of the closure of the image of
`v ↦ vA` on `ℓ²G^m`. A *Sylvester rank function* `rk'` on `Z[G]` is a function on all matrices with
the Malcolmson axioms: `rk'(1) = 1`, `rk'(AB) ≤ min`, additivity on block-diagonal matrices, and
`rk'([A C; 0 B]) ≥ rk'(A) + rk'(B)`. Examples are the rank over a division ring `E` along a ring map
`Z[G] → E`, `rank ρ(A)/d` for a representation `ρ : G → GL_d(E)`, and `rk_G` itself. Say that `rk'`
has *characteristic zero* if `rk'(n) = 1` for every nonzero integer `n`. Its *trivial kernel* is
`N' = {g ∈ G : rk'(1 − g) = 0}`, a normal subgroup.

## Theorem A (dominance forces local indicability)

Let `rk'` be a Sylvester rank function on `Z[G]` of characteristic zero with `rk_G(A) ≥ rk'(A)` for
every matrix `A` over `Z[G]`. Then its trivial kernel `N'` is torsion-free and locally indicable.

In characteristic `p` (`rk'(p) = 0`), every nontrivial finitely generated subgroup of `N'` maps onto
`Z/p`.

Special cases:
- **Augmentation.** `rk_G ≥ rank_Q ∘ ε` on all matrices forces `G` to be locally indicable.
- **Universal localization.** If `Q[G]` has a universal division ring of fractions (in Cohn's sense)
  whose rank function is `rk_G`, then `G` is locally indicable.
- **Quotients.** If `rk'` factors through `G → G/N`, then `N ≤ N'`, so dominance forces `N` to be
  locally indicable. When `G/N` is locally indicable, `G` is.
- **Representations.** If `rk' = rank ρ / d` for `ρ : G → GL_d(C)`, then `ker ρ` is locally
  indicable. If `ρ` has finite image, `G` is virtually locally indicable.

## Theorem B (one-cell asphericity as a rank statement, and what dominance reaches)

Let `L` be a finite contractible 2-complex with one vertex, `e` a 2-cell, `K = L − e`, `G = π₁(K)`,
with generators `x₁, …, x_g`, relators `R₁, …, R_{g−1}` of `K` and boundary word `r` of `e`. Let
`M ∈ M_g(Z[G])` be the Fox matrix whose rows are `∂R_i/∂x_j` (`i < g`) and `∂r/∂x_j`.

1. `ε(M) ∈ GL_g(Z)`.
2. `rk_G(M) = g` if and only if `b₁^(2)(G) = 0`, and then `K` is aspherical.
3. Suppose a proof of `rk_G(M) = g` goes through a characteristic-zero Sylvester rank function `rk'`
   with `rk'(M) = g` and `rk_G ≥ rk'` on all matrices. Then the trivial kernel of `rk'` is locally
   indicable. When `rk'` factors through a locally indicable quotient of `G` (the augmentation, the
   abelianization `G → Z` with `Q(t)`, a torsion-free-abelian-by-infinite-cyclic quotient, and so on; a torsion-free metabelian quotient is not enough, as the Hantzsche--Wendt group shows), `G` itself is
   locally indicable. Such `K` are already aspherical by
   `locally-indicable-2-complex-with-h2-zero-is-aspherical`.

## Calibration

- **Free groups.** Dominance holds for `F₂`: Cohn's free field is universal and is the Linnell
  division ring (recalled, not pinned).
- **Finite groups.** Dominance fails, as Theorem A says it must. The norm element of an element of
  order `n` has augmentation `n` but `rk_G = 1/n`.
- **Hantzsche--Wendt group.** `P = ⟨x, y | x⁻¹y²xy², y⁻¹x²yx²⟩` is torsion-free and amenable, with
  `H₁ = (Z/4)²`. The presentation complex has `χ = 1` and `b₁^(2) = 0`, so `rk_P(∂₂) = 1`, while
  `ε(∂₂) = [[0,4],[4,0]]` has rank 2 over `Q`. Dominance fails at the augmentation, although `Q[P]`
  is an Ore domain.
- **Homology spheres.** A closed hyperbolic homology 3-sphere with group `Γ` has a spine with `χ = 1`.
  Its Fox matrix has unimodular augmentation but `rk_Γ(∂₂) = g − 1` (Lott--Lück `b₁^(2)(Γ) = 0`,
  recalled). So even unimodularity plus torsion-freeness gives no dominance.

## Faithful quotient rank functions add nothing (Step 6 of the proof)

Every Sylvester rank function `rk'` on `Z[G]` factors through `Z[G/N']`. Call the induced rank
function *faithful* when a nonzero row `x` over `Z[G/N']` with `xB = 0` forces `B` to have less than
full row rank. Examples are the von Neumann rank and the rank over a division ring containing
`Z[G/N']`.

**Proposition.** In the setting of Theorem B, let `N ⊴ G` be locally indicable and let `rk''` be a
faithful rank function on `Z[G/N]` with `rk''(πM) = g`. Then the regular cover `K_N` has
`H₂(K_N) = 0`, so `K_N`, and hence `K`, is aspherical by
`locally-indicable-2-complex-with-h2-zero-is-aspherical`. No rank comparison with `rk_G` is needed.

## What survives

The obstruction is for rank comparisons that hold on *all* matrices. The Proposition also removes
the transfer inequality `rk_G ≥ rk_{G/N} ∘ π` across a locally indicable normal subgroup `N`.
Whether or not that inequality holds, its hypothesis `rk_{G/N}(πM) = g` already gives asphericity
by Howie on the cover `K_N`. By Theorem A, a dominated `rk'` whose induced rank function on
`Z[G/N']` is faithful is covered in the same way. What is left:
- comparisons for the single matrix `M`;
- dominated rank functions whose induced rank function on `Z[G/N']` is not faithful (for example
  `rank ρ/d` for a representation that is not injective on the group ring);
- approximation arguments, where `rk_G = lim rk'_i` and no single `rk'_i` has full rank on `M`.
