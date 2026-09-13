---
rg: 2
id: pmf-permanence-amenable-kernel-without-exactness
kind: claim
title: Semidirect products with residually finite amenable kernel inherit strongly convergent representations from the quotient, with no exactness hypothesis
distinct_from:
  gkmp-amalgam-product-mf-permanence: that is permanence for amalgams G *_H (H x L) through selflessness and needs exactness; this is permanence for A x| Q with amenable kernel, proved by finite affine actions and Fell absorption, with no exactness.
  binary-jacobson-gkm-semidirect-hypotheses-fail: that checks the hypotheses of the published extension theorem against one extension and finds they fail; this is a version of that theorem with a weaker hypothesis and a different proof.
---

ESTABLISHED (unreviewed).  Let `Q` be a countable group with
finite-dimensional unitary representations `sigma_n -> lambda_Q` strongly.  Let
`A` be a countable amenable group with a `Q`-action by automorphisms and a chain
`A = A_0 >= A_1 >= ...` of `Q`-invariant finite-index subgroups with trivial
intersection.  Then `A x| Q` is purely matricial field (PMF), and PFF if the
`sigma_n` have finite image.  The representations are
`pi_N (x) sigma_n`, with `pi_N` the permutation representation of the affine
action on `A/A_N`, and `N`, `n` taken to infinity along a diagonal.

This recovers the PMF and PFF cases of Gao--Kunnawalkam Elayavalli--Mj,
arXiv:2607.29571v1, Theorem 1.1 ("Let G be a finitely generated residually
finite amenable group and L be an exact MF/PMF/PFF group. Then G⋊L is
MF/PMF/PFF.") without assuming `L` exact: a finitely generated residually
finite group has a characteristic chain.  GKM remark that for direct products
preservation of strong convergence "is unknown in the absence of this
assumption".  When one factor is amenable and residually finite, the proposition
removes that assumption.

Proof: `pmf-permanence-amenable-kernel-without-exactness-proof`.
