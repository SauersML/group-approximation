---
rg: 2
id: order-preserving-lattice-automorphisms-are-solvable-proof
kind: route
title: Infinitesimality is order-theoretic, so the flag of kernels is invariant
target: order-preserving-lattice-automorphisms-are-solvable
requires: []
---

## Why sufficient

**The shape of a bi-invariant order on `Z^n`.**  A translation-invariant total
order on `Z^n` is given by a positive cone `P` with `P` disjoint-union `-P`
disjoint-union `{0}` equal to `Z^n` and `P + P` contained in `P`.  Such orders
are exactly the lexicographic stacks of linear functionals: there are
`f_1, ..., f_m` in the dual of `R^n` such that `x > 0` iff the first
`f_i(x)` that is nonzero is positive, and the common kernel meets `Z^n` in `0`.

**The flag is order-theoretic, hence invariant.**  Call `x` *infinitesimal* if
`|x| < y` for every `y > 0` with `y` not infinitesimal — concretely, `x` is
infinitesimal exactly when `f_1(x) = 0`.  This is defined purely from the order,
so any order-preserving automorphism `A` maps infinitesimals to infinitesimals:
`A` preserves `ker f_1 intersect Z^n`, and therefore its real span `ker f_1`.
Iterating inside `ker f_1` with `f_2`, and so on, `A` preserves the whole flag
`ker f_1 > ker f_1 intersect ker f_2 > ...`.

**Positive scalars on the quotients.**  On each one-dimensional quotient of
consecutive flag terms, `A` induces an order-preserving automorphism of an
ordered one-dimensional real vector space, which is multiplication by a positive
scalar.

**Solvability.**  So in a real basis adapted to the flag, every element of
`Gamma` is upper triangular with positive diagonal entries.  The group of real
upper-triangular matrices is solvable, and subgroups of solvable groups are
solvable, so `Gamma` is solvable.

## Sharpness

The conclusion is about the *image* in `GL_n(Z)`, not about `Gamma` itself: a
non-solvable `Gamma` acting through a solvable image is not excluded, but then
the action has a large kernel and the pair has no relative (T) either.

The statement is genuinely about bi-orders.  It fails for left-orders:
`Z^2 semidirect F_2` is locally indicable, hence left-orderable, and the
argument breaks at the first step because a left-invariant order on the normal
subgroup need not be preserved by conjugation.
