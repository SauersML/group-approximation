---
rg: 2
id: rank-one-closure-excludes-noncentral-outlier-gauges
kind: claim
title: Rank-one closure excludes noncentral multiplicity gauges on SL3 outliers
distinct_from:
  rank-one-conjugacy-kills-c2-congruence-fold: that proves exact and torus-robust collapse only for discrete central C2 signs over an exact odd-congruence actor; this asks for the missing extension to noncentral gauges and non-congruence ambient outliers.
---

OPEN.  In every regular-type ambient-extension outlier satisfying the closed
two-return `A_2` loop, the genuine rank-one conjugacy

```text
W_12E_12W_12^*=B_21
```

forces the denominator fold square to approach one.  Equivalently, every
noncentral multiplicity gauge which evades the discrete `C_2` sign theorem
must pay a dimension-free defect in this conjugacy, one of the two mixed
returns, or the unbalanced torus word.

The exact central-sign sector is established.  What remains is a
same-carrier theorem converting an arbitrary approximate actor outlier into
that sector or directly charging its noncentral gauge.  No scalar sheet
character remains available as a counterexample.

`rank-one-closure-reduces-to-noncentral-gauge` now closes the larger
near-central sector for arbitrary sheet operators: if their distance to the
block-scalar center tends to zero, the fold-Gram defect tends to zero with an
explicit dimension-free bound.  Thus this claim has been reduced to gauges
which stay uniformly noncentral, together with genuinely non-congruence actor
outliers.

The first authenticated denominator-crossing test also closes a genuinely
noncentral, but still linear, part of that residual.
`authenticated-mixed-loop-kills-natural-affine-gauges` imposes the mixed word

```text
[h x_21(-1) h^(-1),x_13(1)]=h^(-1)x_23(-1)h
```

on the same honest coefficient carrier as the rank-one conjugacy and the two
closed returns.  Its two affine Fox rows force every natural-module
translation gauge to vanish, uniformly over multiplicity.  What remains here
is therefore not the obvious natural affine extension: it is an arbitrary
unitary/nonlinear gauge, a different coefficient module, or a noncongruence
actor outlier.  Upgrading that scoped detector to those sectors is still the
common-carrier/exactification problem, not another missing scalar relation.

The linear sector is now larger than copies of the defining module.
`authenticated-mixed-loop-kills-minuscule-affine-modules` computes the dual
Fox rows and uses extension closure to kill every defining-characteristic
module whose composition factors are trivial, defining, contragredient, or
Frobenius twists of those.  The remaining linear question is the literal
two-row group-algebra problem for the other highest-weight blocks; it is not
hidden inside multiplicity or nonsplit-extension bookkeeping.

`authenticated-mixed-loop-kills-quadratic-affine-modules` further computes
the rows on the symmetric square.  In odd characteristic this also kills the
full tensor square of the defining module, and extension closure propagates
the result to every module filtered by the degree-zero, degree-one, and this
degree-two block.  Consequently the first polynomial nonlinear block is not
the missing affine enemy either.

`authenticated-mixed-loop-kills-bilinear-affine-modules` also closes the
mixed tensor `M tensor M^*=End(M)`.  The calculation is uniform in every odd
characteristic and does not split off the scalar summand, so it covers the
adjoint-type corrector even in characteristic three.  The unresolved linear
sector has therefore moved past every tensor product of two copies chosen
from the defining and contragredient coordinates: the quadratic calculation
also closes the dual symmetric square, while the bilinear calculation closes
the mixed tensor.
