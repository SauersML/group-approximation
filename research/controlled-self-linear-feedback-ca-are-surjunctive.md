---
rg: 2
id: controlled-self-linear-feedback-ca-are-surjunctive
kind: claim
title: Injective automata whose block rows are linear in their own block under nonlinear controllers are surjective
distinct_from:
  recipient-affine-three-factor-ca-are-surjunctive: that allows a pure-others offset in each row with a constant own coefficient, a class universal for Gottschalk's conjecture; this forbids offsets and lets the own coefficient depend nonlinearly on the other blocks, which makes surjunctivity provable over every group.
  certificate-controlled-routing-is-surjunctive: that routes each output datum from one input datum under a preserved certificate; this has no preserved certificate and lets every row combine its own block linearly under nonlinear control.
  central-c3-quadratic-surjunctivity-iff-direct-finiteness: that is same-track quadratic feedback on a central three-cycle, equivalent to direct finiteness; this excludes nonlinearity in a row's own block and needs no hypothesis on the group.
  common-factor-power-actor-ca-are-surjunctive: that is a same-track Boolean quadratic family; this has no same-block nonlinearity at all.
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

Let `G` be any group and `R` a finite ring. Partition the tracks into blocks
`X_1, ..., X_r`, block `a` with alphabet `R^(d_a)`. Suppose a cellular
automaton `F` on the product full shift has rows

    F_a(x)(g) = X_a(g) + sum_(s in S) C_(a,s)(x)(g) . X_a(g s),

where `S` is finite and each controller `C_(a,s)` is a local
`M_(d_a)(R)`-valued function reading no coordinate of block `a`, with any
nonlinearity in the other blocks. Suppose each constant automaton
`X_a -> X_a + sum_s C_(a,s)(0) . R_s X_a` is bijective. This holds for
instance when the controllers vanish once all other blocks vanish.

If `F` is injective, then `F` is surjective.

The proof is induction on `r` through a two-block lemma. That lemma
straightens the first block with the certificate-fiber theorem and reads
surjectivity off the zero fiber.

Scope:
- It contains the bipartite quadratic and target-multiplicative theorems of
  the 09-08 block-elimination artifact.
- It extends them to controllers of any degree, any memory and any number of
  other blocks.

Every hypothesis is a sharp boundary, as the artifact shows:
- Dropping invertibility of the constant own part admits every linear
  automaton, so Kaplansky's stable finiteness question for `R[G]`.
- Allowing pure-others offsets admits the universal recipient-affine normal
  form, so all of Gottschalk's conjecture.
- Allowing own-block nonlinearity admits the central three-cycle family, so
  direct finiteness in characteristic two.

A counterexample must keep one of these three features in every presentation.

This is a class theorem. It does not prove Gottschalk's conjecture for any
group.
