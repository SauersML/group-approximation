---
rg: 2
id: moutzouris-singular-subgroup-has-vanishing-trace
kind: claim
title: A singular subgroup of K_0 of a unital exact stably finite Q-stable algebra is annihilated by some tracial state (Moutzouris)
distinct_from:
  moutzouris-faithful-trace-zero-class-both-signs: that imports the realisation tool (Theorem 4.1) and Proposition 4.3 on sign control; this imports the ordered-group existence of a state vanishing on a singular subgroup and the class G of Proposition 5.1.
  stw07-singular-classes-change-sign-or-sit-on-boundary: that says one singular class is never strictly one-signed on traces; this gives a single trace vanishing on a whole singular subgroup.
artifacts:
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

**Established (literature).**  I. Moutzouris, *Extensions of quasidiagonal
C\*-algebras and controlling the K_0-map of embeddings*, arXiv:2112.03224v3,
read from the PDF on 2026-09-13.

1. (Proposition 2.6)  The positive cone of `K_0(A ⊗ Q)` is
   `{x ⊗ y : x ∈ K_0(A)^+, y ∈ Q_(≥0)}`.
2. (Lemma 2.12)  Let `(G, G^+, u)` be a scaled ordered countable abelian group
   with `G ≅ G ⊗ Q` via an order isomorphism, `H_1 ⊆ G` a subgroup with
   `H_1 ∩ G^+ = {0}`, and `H_2 ⊆ G` a subsemigroup with `H_2 ∩ -G^+ = {0}` and
   `H_2 ∩ -H_2 = H_1`.  Then there is a state `ρ` with `ρ(H_1) = 0` and
   `ρ(x) ≥ 0` for every `x ∈ H_2`.
3. (Remark 2.13 and (2.5))  If `A` is separable, exact, stably finite, unital
   and Q-stable, and `G ≤ K_0(A)` is singular, then some `τ ∈ T(A)` has
   `τ^(G) = 0`.  The map `T(A) -> S(K_0(A))` is onto for exact `A`, citing
   Haagerup [15, Thm. 5.11] and Blackadar--Rørdam [3, Thm. 3.3].  If every state
   on `K_0(A)` is induced by a faithful trace, `τ` can be taken faithful.
4. (Proposition 5.1)  Every separable unital nuclear quasidiagonal UCT algebra
   in which every state on `K_0` is induced by a faithful trace has the
   K_0-embedding property.
5. (Example 4.6)  In `C(S^2) ⊕ C` the singular class `(0, 1, -1)` is annihilated
   by no state induced by a faithful trace.

The Q-stability in item 3 is removed for singular subgroups of stably finite
algebras in Lemma A of the artifact.  Tensoring with `Q` keeps a singular
subgroup singular, and a trace on `A ⊗ Q` restricts to `A ⊗ 1`.
