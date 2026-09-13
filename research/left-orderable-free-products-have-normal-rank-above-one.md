---
rg: 2
id: left-orderable-free-products-have-normal-rank-above-one
kind: claim
title: Free products of two nontrivial left-orderable groups have normal rank greater than one
distinct_from:
  klyachko-kl-holds-for-torsion-free: that concerns G * Z with a relator of exponent sum ±1 over any torsion-free G; this concerns A * B with both factors left-orderable and any relator not conjugate into A, and for B = Z it drops the exponent-sum condition for left-orderable A.
  wiegold-problem-has-finitely-presented-counterexamples: that is the existence answer to Wiegold's question; this is the normal-rank theorem it is derived from.
---

**ESTABLISHED** by `left-orderable-free-product-normal-rank-citation` (literature
import, not reproved).

**Statement.** Let `A` and `B` be nontrivial left-orderable groups, and let `w` be
an element of `A * B` that is not conjugate into `A`. Then the natural map
`A -> (A * B)/<<w>>` is injective. Consequently `A * B` has normal rank greater
than 1: no single element normally generates it.

**Consequences.**
- **Factors with orderable quotients.** The same normal-rank bound holds whenever
  each factor merely admits a nontrivial left-orderable quotient: map `A * B` onto
  the free product of those quotients. The source remarks this at l.204, and
  `normal-rank-one-free-products-need-cyclic-abelianization` uses it.
- **The case `B = Z`.** Here the statement is the Levin conjecture for
  left-orderable `A`: `A` injects into `(A * Z)/<<w>>` whenever `w` is not
  conjugate into `A`, with no condition on the exponent sum (source l.231).
  Klyachko's theorem (`klyachko-kl-holds-for-torsion-free`) covers every
  torsion-free `A`, but needs exponent sum ±1.
- **Not part of this claim.** The same paper proves that the image of `u` in
  `(A * B)/<<u^k>>` has order exactly `k` when `u` is not conjugate into a factor
  and is not a proper power (Corollary `cor: torsion`, l.1470–1473).
