---
rg: 2
id: paradoxical-steinberg-families-kazhdan-no-mf-quotient
kind: claim
title: Boundary-action and self-similar Steinberg algebras have properly infinite units, so their elementary groups have no nontrivial MF quotient, and over finite fields they are finitely generated Kazhdan
distinct_from:
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that is the abstract criterion for simple rings; this names explicit finitely generated algebras, from free group boundary actions and from arbitrary self-similar actions, where the criterion holds.
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that treats every groupoid without invariant measure, at rank 2n; these families have a properly infinite unit, so rank 2 suffices and no Tarski input is needed.
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

Let `k` be a countable field. Each ring `R` below has a properly infinite unit, `2[1] <= [1]` in
`V(R)`. So for every `N >= 2`, every homomorphism from `EL_N(R)` to an MF group is trivial.

If `k` is finite, `R` is also a finitely generated ring, and `EL_N(R)` is a finitely generated Kazhdan
group for `N >= 3`.

**Corrected 2026-09-13 (un-verify).** The first landing claimed finite generation and (T) for every
countable field. That is false for infinite `k`. A finite subset of `EL_N(R)` has entries in a subring
with coefficients in a finitely generated subring `A ⊊ k`; the subring is proper because a field that
is finitely generated as a ring is finite. So `e_12(λ)` with `λ ∈ k \ A` is not in the generated
subgroup. `EL_N(R)` is then not finitely generated and has no (T). The no-MF-quotient clause holds for
every countable `k`.

1. **(F1) Boundary actions.** `R = LC(∂F_d, k) ⋊ F_d` for `d >= 2`: the algebraic crossed product of
   the free group acting on the space of infinite reduced words. It is the same construction as the
   Pestov 9.1 ring `LC(X, F_q) ⋊ Z`, with the measure-carrying minimal Z-subshift replaced by the
   paradoxical boundary action.
2. **(F2) Self-similar actions.** `R = A_k(𝒢_(G,X))`, the Steinberg algebra (span of compact open bisection
   indicators) of the groupoid of germs of a self-similar action `(G, X)`, with `G` finitely generated
   and `|X| >= 2`.
   - Hausdorffness is not needed.
   - The prefix bisections give a unital copy of `L_k(1,|X|)`.

Simplicity of `EL_N(R)` modulo its centre is not claimed here.

Unreviewed proof in the artifact, Section 4.
