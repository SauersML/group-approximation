---
rg: 2
id: culf-mastel-rstar-uniform-fano-cap-profile
kind: claim
title: Uniformly select a Fano-cap affine support branch for the Culf--Mastel R-star family
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for any effective perfect-gap LCS compilation; this isolates the narrower one-ghost support-profile selector after local affine soundness is proved.
  bcs-to-lcs-exact-support-gap: that asks for one static exact robust sub-menu; this must work uniformly over the machine-indexed Culf--Mastel family and preserve its RE orientation.
---

OPEN.
Starting from the fixed `R_*` perfect-gap family now supplied directly by
`culf-mastel-rstar-fixed-language-gap-is-published`, effectively output one
finite marked LCS instance such
that:

```text
M halts     => some perfect CE R_* strategy is represented on a
               Fano-cap support profile and gives J != 1,
M nonhalts  => every marked approximate LCS model would restrict to a
               perfect CE R_* strategy.                              (UFC1)
```

For any **fixed** cap profile, the local affine replacement is sound by
`rstar-fano-cap-support-preserves-nonru-affine-relaxation`.  The finite OR
operation itself is now supplied by
`finite-lcs-product-sign-is-exact-or`: homogenize branch `i` with a private
central selector `Z_i`, impose `product_i Z_i=J`, and priority-decompose the
odd selector sector.  Unlike identifying all branch signs, this is an OR
and remains an ordinary finite LCS with one authenticated mark.

The missing operation is therefore earlier: effectively produce a finite
menu of cap-profile affine branches for which **some** branch retains a
perfect model on every halting instance.  Once that finite complete menu is
available, its sound branches can be combined without choosing a profile
uniformly in advance.

## Attempts

Pairwise pruning removes an atom with no compatible neighbor, and
`commuting-neighborhood-pruning-pays-atom-mass` removes an atom with no joint
extension when all neighbor PVM algebras commute.  General oracular 2-CSP
strategies do not provide that mutual neighborhood commutation.  Even if
one proves that every perfect model prunes to one of a computably listed
finite set of cap profiles, model-dependence of the chosen profile is no
longer an obstruction: the product-sign OR compiler combines the list.  What
is not established is that pruning/completeness theorem, nor the required
fixed-language quantum reduction producing the list.

The recursion-theoretic orientation is otherwise correct.  Culf--Mastel give
perfect CE completeness on `HALT` and a constant CE gap on `NONHALT`, exactly
the orientation required by `re-oriented-lcs-compiler-gives-nonhyperlinear-group`.
What is conditional is the uniform cap-profile compiler, not the Kleene
branch direction.

The fixed-language part is no longer conditional.  Theorem 4.14 and
Corollaries 4.17--4.18 of Culf--Mastel apply directly to the Boolean,
non-TVF relation `R_*`.  Their commutation weights remain contextwise,
however, and therefore do not supply the mutually commuting neighborhoods
assumed by the stronger pruning step.
