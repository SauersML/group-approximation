---
rg: 2
id: finite-simple-rr0-algebras-have-weak-cancellation
kind: claim
title: Every finite simple unital C*-algebra of real rank zero has weak cancellation
distinct_from:
  stw99-problem-lx-rr0-weak-cancellation: that asks for weak cancellation of ALL real rank zero algebras (plus K1-surjectivity); this is its restriction to finite simple unital algebras, which is exactly the range where it decides Rordam's dichotomy.
---

Let `C` be a unital simple C\*-algebra of real rank zero whose unit is finite.
Does `C` have weak cancellation, i.e. do `p direct_sum r ~ q direct_sum r`
and fullness of `p, q` (automatic by simplicity for nonzero projections) imply
`p ~ q`?

Rordam (*The real rank of certain simple C\*-algebras*, 2005, page 1) records
that it is unknown whether all finite simple C\*-algebras have weak
cancellation.  The present claim is the real-rank-zero case.

A positive answer settles Problem XXIX
(`stw29-via-finite-simple-rr0-weak-cancellation`).  It is implied by LX(1)
(`finite-simple-rr0-weak-cancellation-via-lx`) and by stable rank one of finite
simple real-rank-zero algebras
(`finite-simple-rr0-weak-cancellation-via-stable-rank-one`).

## Attempts

* Counterexamples here are exactly what XXIX needs.  By
  `stw29-counterexample-level-two-fingerprint`(c), any finite corner `C` of a
  mixed simple real-rank-zero algebra violates weak cancellation with the
  explicit pair `[1_C]`, `[1_C] + r`.  Conversely a stably finite failure of
  weak cancellation would not touch XXIX.  The two problems split along
  whether the witness `r` absorbs the doubled unit.
* Known cancellation failures in simple algebras are not of real rank zero.
  Villadsen's stably finite examples and Rordam's mixed examples
  (`rordam-mixed-examples-not-real-rank-zero`) break cancellation through
  Euler classes of bundles over high-dimensional products, and the same Euler
  classes survive Villadsen transversality on the zero sets of generic
  self-adjoint perturbations.
* For simple algebras weak cancellation is the same as separativity of
  `V(C)` (`stw29-separative-projection-monoid-dichotomy`).  It therefore holds
  for simple inductive limits of blocks with separative `V`: stable rank one,
  purely infinite simple, tame `V`.  A proof for all finite simple
  real-rank-zero algebras needs analytic input beyond the monoid, since
  `opr-mixed-simple-refinement-monoid` rules out purely monoid-theoretic
  arguments.
