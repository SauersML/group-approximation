---
title: STW LXXXIV checkpoint --- split common infinite stabilizers (2026-08-30)
---

## The theorem

Let `A=H direct_sum Q`, where `H,Q` are countable abelian groups of finite
rational ranks `h,q`.  Suppose `H` acts trivially on a countable set `S` and
the residual `Q`-action has finite point stabilizers.  For every countable
locally finite lamp `L`, put

`G=(direct_sum_S L) rtimes A`.

Then, for `q>=1`,

`h+q <= dim_nuc C*(G) <= (h+1)(q+1)9^q-1`.

For `q=0`, the exact value is `h`.

This is the first positive class in this lane with infinite point
stabilizers: `A_s=H direct_sum Q_s` has rational rank `h`, while the finite
groups `Q_s` need not have uniformly bounded order.

## Why the bound is safe

The group factors exactly as

`G=H times ((direct_sum_S L) rtimes Q)`.

The corrected finite-stabilizer theorem bounds the second factor by
`(q+1)9^q-1`.  Tensoring with `C*(H)=C(H_hat)`, of nuclear dimension `h`,
gives the upper bound.  Killing the lamp group gives the abelian quotient
`A`, hence the lower bound `h+q`.  When `q=0`, the second factor is locally
finite, so locally finite direct-factor invariance gives equality.

Fiberwise, the residual scalar case is `C*(N)` and costs at most `q`; a
non-scalar residual Bernoulli fiber costs at most one.  The common `H`
directions are trivial, not strongly outer, and are therefore extracted as
the tensor factor `C*(H)`.  This is exactly where the factor `h+1` comes
from.

## Strictness and remaining obstruction

Take `H=Z`, `Q=Z direct_sum direct_sum_n Z/2`, let `S` be the disjoint union
of the coset actions `Q/<e_n>`, and use lamp `Z/2`.  Every stabilizer is
infinite of rank one, and kernel-finiteness fails, but the theorem gives the
finite interval `2<=dim_nuc<=35`.

This does not cover orbit-dependent infinite stabilizers with no common
split core.  In that setting a fixed fiber has the form

`tensor_R tensor_(K/H_R) M_(n_R)`

for varying positive-rank subgroups `H_R`.  There is no single free
Bernoulli regrouping `B^(tensor K)` and no common commutative tensor factor
to extract.  Uniform bounds on the individual ranks `rank(H_R)` do not
produce a common subgroup of comparable rank—their intersection can collapse
to zero—and do not supply such a splitting.  A new theorem for these mixed
homogeneous-space tensor actions is still required.
