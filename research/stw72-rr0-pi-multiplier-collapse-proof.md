---
rg: 2
id: stw72-rr0-pi-multiplier-collapse-proof
kind: route
title: Give the multiplier topological dimension zero and invoke the weak-to-plain collapse
target: stw72-rr0-pi-multiplier-is-purely-infinite
requires:
  - stw72-topdim-zero-wpi-is-purely-infinite
artifacts:
  - research/artifacts/stw72-topdim-zero-literature-import-2026-08-30.md
---

Let `A` satisfy the target's hypotheses.  Zhang's multiplier ideal theorem,
packaged as Ng--Thiel--Vilalta, [Theorem
2.6](https://doi.org/10.1112/blms.70343), says that `M(A)` has topological
dimension zero: every closed ideal of `M(A)` is the closed linear span of its
projections, so `M(A)` has the ideal property, which implies topological
dimension zero.

Kirchberg--Rordam, Proposition 4.11 of [*Non-simple purely infinite C-star
algebras*](https://doi.org/10.1353/ajm.2000.0021), says that the multiplier
algebra of a sigma-unital purely infinite C-star algebra is weakly purely
infinite.  Thus `M(A)` is both weakly purely infinite and of topological
dimension zero.  The established claim
`stw72-topdim-zero-wpi-is-purely-infinite` now gives that `M(A)` is purely
infinite.  This is exactly Ng--Thiel--Vilalta, Corollary 2.8.
