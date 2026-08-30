---
rg: 2
id: stw81-continuous-simple-af-fields-have-base-bound
title: Continuous fields with simple unital AF fibres inherit the base dimension bound
kind: claim
distinct_from:
  stw81-one-dim-simple-af-fields-have-dim-one: that result assumes local triviality and uses bundle charts; this result allows arbitrary continuous fields and varying simple AF fibres by lifting finite-dimensional fibre models through shrinking-neighborhood quotients.
  stw81-zero-dim-simple-fields-obey-trichotomy: that result allows arbitrary simple nuclear fibres over a zero-dimensional base; this result permits every finite-dimensional base but requires unital AF fibres.
  stw81-one-dim-elementary-oinfty-fields-have-dim-one: that theorem uses local triviality and absorption for its non-type-I fibres; this theorem treats non-locally-trivial stably finite fields using semiprojectivity.
artifacts:
  - research/artifacts/stw81-continuous-af-field-audit-2026-08-30.md
---

# Continuous fields with simple unital AF fibres inherit the base dimension bound

## Theorem

Let `A` be a separable continuous `C_0(X)`-algebra, where `X` is a
second-countable locally compact Hausdorff space of finite covering dimension.
If every fibre `A_x` is a unital AF algebra, then

```text
dim_nuc(A) <= dim(X).
```

If, in addition, every fibre is simple and non-elementary, then every ideal
quotient of `A` has no nonzero commutative hereditary subalgebra.

Consequently, if `dim(X)<=1` and every fibre is an infinite-dimensional
simple unital AF algebra, possibly varying with `x`, then `A` satisfies the
hypothesis of Problem LXXXI and

```text
dim_nuc(A) belongs to {0,1}.
```

No local triviality, local constancy of the fibre isomorphism class, or
classification of AF algebras is used.

## New mechanism

At a point `x`, approximate the relevant fibre values inside a
finite-dimensional subalgebra `E_x` of `A_x`. Write the fibre as the quotient
`A/I_x`. The ideal `I_x` is the closure of an increasing union of ideals
which cut away successively smaller neighborhoods of `x`. Semiprojectivity
of `E_x` therefore lifts its inclusion in `A_x` to an exact
star-homomorphism over some closed neighborhood of `x`.

The lifted finite-dimensional model and each original section agree within
the prescribed tolerance at `x`; continuity shrinks this to a neighborhood
on which they remain close. A coloured refinement of these neighborhoods and
central cutoffs then gives the nuclear-dimension approximation. The fibre
models cost no colour because their return maps are exact order-zero maps.

## Boundary of the argument

For a simple fibre of nuclear dimension one, its finite-dimensional
approximation returns by order-zero maps rather than star-homomorphisms.
Their cones need not be semiprojective, so this neighborhood-lifting proof
does not extend formally to Jiang--Su-stable fibres. The exact point where
the AF hypothesis enters is therefore the semiprojective lift of an honest
finite-dimensional subalgebra, not local triviality of the field.

