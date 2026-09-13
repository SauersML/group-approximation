---
rg: 2
id: bernoulli-factor-algebraic-actions-have-finite-stabilizers
kind: claim
title: An algebraic action that is a factor of a Bernoulli shift has finite stabilizers on every nonzero module element
distinct_from:
  bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial: that shows Borel equivariant maps from a Bernoulli shift into coset shifts with infinite stabilizers are constant; this shows the dual of a module with an infinitely stabilized nonzero element is not a Bernoulli factor at all, through one invariant character.
  koopman-lambda-singular-part-has-zero-rokhlin-entropy: that locates Rokhlin entropy in the part of the Koopman representation not singular to lambda; this is the elementary fact that a Bernoulli factor carries no unit vector invariant under an infinite subgroup, applied to algebraic actions.
---

**ESTABLISHED** by [[bernoulli-factor-algebraic-actions-finite-stabilizers-proof]].

Let `G` be a countable group and `M` a countable left `Z[G]`-module. Let
`X_M = Hom(M, T)` be its Pontryagin dual, with Haar measure `m_X` and the dual action
`(g.x)(a) = x(g^-1 a)`. Suppose `G ↷ (X_M, m_X)` is a factor of a Bernoulli shift
`G ↷ (L^G, lambda^G)` over some standard probability space `(L, lambda)`. Then

    Stab_G(a) = { g in G : g a = a }   is finite for every nonzero a in M.

Consequences used in this graph:
- Every nonzero element of `F_p[G]^n` has a finite stabilizer, so the test is passed by
  every module that embeds in a free module, in particular by projective summands
  (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`).
- Over the binary Leavitt unit group, every nonzero module over the Leavitt algebra has a
  nonzero element with infinite stabilizer, so none of its dual actions is a Bernoulli
  factor (`leavitt-module-dual-actions-are-self-squares-off-bernoulli`).
- If `X × B ≅ B'` with `B, B'` Bernoulli, then `X` is a factor of `B'`. So an algebraic action
  failing the test is never a *Bernoulli complement*, and cannot turn one Bernoulli shift
  into another of different base entropy.
