---
rg: 2
id: stw07-quotient-trace-zero-nontorsion-class-is-killed
kind: claim
title: A class vanishing on a trace whose kernel quotient is UCT and sees it rationally is killed by a faithful model
distinct_from:
  moutzouris-faithful-trace-zero-class-both-signs: that concerns a faithful trace on the algebra itself; this passes to the quotient by an arbitrary trace kernel and balances against a faithful model of the ambient algebra.
  stw07-sign-changing-qd-trace-values-kill-class: that needs two traces of opposite sign; this needs one zero trace and non-torsion in its kernel quotient.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED (Theorem G of the artifact).**  Let `A` be separable, unital,
nuclear and quasidiagonal, and `x in K_0(A)`.  Suppose some tracial state
`tau` has `tau^(x)=0`, the quotient `A/J_tau` by its trace kernel satisfies
the UCT, and the image of `x` in `K_0(A/J_tau)` is not torsion.  Then some
asymptotically multiplicative, asymptotically isometric c.c.p. maps
`A -> M_(k_n)` have value `0` on `x`.

No faithful trace, UCT hypothesis or trace quasidiagonality is required of
`A` itself.

Proof.  Apply Proposition 4.3 to the faithful trace induced on `A/J_tau`.
That gives faithful AF embeddings of the quotient with strictly positive and
strictly negative values on the image of `x`.  Composed with the quotient
map and with finite-stage compressions of the AF algebras, they are models
of `A` whose values are eventually `>0` and `<0`.  Balance a faithful model
of `A` against them with `n`-dependent multiplicities, as in
`stw07-sign-changing-qd-trace-values-kill-class`.
