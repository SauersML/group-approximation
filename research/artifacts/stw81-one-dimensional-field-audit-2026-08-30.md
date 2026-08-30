---
title: STW LXXXI audit --- one-dimensional elementary/O-infinity fields and the clopen obstruction (2026-08-30)
---

## Positive one-dimensional field class

Let `A` be a separable nuclear locally trivial field of simple C-star
algebras over a second-countable locally compact base `X` with
`dim(X)<=1`.  Assume every fibre is either elementary or
O-infinity-stable.  Local triviality makes these two fibre loci clopen.

On the elementary locus, the field is continuous trace.  The
Winter--Zacharias continuous-trace theorem computes its nuclear dimension
as the covering dimension of its spectrum, hence at most one.

On the other locus, fibrewise O-infinity-stability globalizes.  The exact
import is Hirshberg--Rordam--Winter,
[*C0(X)-algebras, stability and strongly self-absorbing C-star algebras*](https://arxiv.org/abs/math/0610344),
Theorem 4.6: if `D` is K1-injective and strongly self-absorbing, `X` is
locally compact metrizable and finite-dimensional, and `A` is a separable
`C_0(X)`-algebra, then `A` is D-stable iff every fibre is D-stable.
Taking `D=O_infinity` makes the field O-infinity-stable.  Then
Bosa--Gabe--Sims--White,
[*The nuclear dimension of O-infinity-stable C-star algebras*](https://arxiv.org/abs/1906.02066),
gives nuclear dimension at most one.  The finite clopen direct sum has
nuclear dimension at most one.

The LXXXI shadow hypothesis also holds.  A commutative hereditary shadow
is Morita equivalent to its generated type-I ideal.  Such an ideal cannot
meet the O-infinity-stable simple-fibre locus, since evaluation would give
a non-type-I quotient.  It therefore lives in a continuous-trace
subquotient over a locally closed subset of the elementary locus and has
spectrum dimension at most one.

## Why the zero-dimensional proof stops

The earlier zero-dimensional theorem uses that `C_0(X)` is AF: finite
sets are approximated on clopen partitions, so the base costs no new
nuclear-dimension colour.  This mechanism fails sharply on a connected
one-dimensional compact space.  It has no nontrivial clopen sets, hence
no finite-dimensional subalgebras of `C(X)` beyond the constants.  The
constant-base models cannot approximate a nonconstant scalar function,
even after tensoring with a nonzero fibre.

The ordinary tensor estimate reflects the resulting cost:

`dim_nuc(C(X) tensor B)
 <= (dim(X)+1)(dim_nuc(B)+1)-1`.

For one-dimensional base and fibre this is three, not one.  The theorem
above reaches one only because continuous-trace geometry or
O-infinity-absorption collapses the colours.

## Remaining frontier

The first locally trivial simple-fibre class not covered is a
one-dimensional base with stably finite, non-elementary simple fibres of
nuclear dimension one.  Fibrewise finite nuclear dimension gives
Z-stability of the fibres, and Hirshberg--Rordam--Winter globalizes that
Z-stability, but no imported theorem computes an arbitrary nonsimple
Z-stable field's nuclear dimension as one.  Applying only the tensor or
extension bounds reintroduces extra colours.  Thus the residual issue is
analytic colour collapse for stably finite Z-stable fields, not primitive
spectrum dimension or local triviality.
