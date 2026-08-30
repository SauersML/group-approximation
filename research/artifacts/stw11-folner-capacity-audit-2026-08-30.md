---
title: STW XI audit --- maximal Folner capacity and faithful invariant measures (2026-08-30)
---

## Result

For an arbitrary action of `Z^d` on a compact metrisable space, the maximal
box-Folner averages obey an exact variational formula: their norm converges
to the maximum integral over all invariant probability measures.  Therefore
positivity of this limit for every nonzero positive continuous function is
equivalent to existence of one faithful invariant probability measure.  The
proof is constructive: each positive function produces an invariant
empirical-orbit limit attaining the variational maximum, and countably many
such limits are mixed to obtain full support.

The operator-algebraic consequence is immediate but useful for Problem XI:
every action satisfying this dynamical criterion has a crossed product that
embeds into a unital simple AF algebra.  Dense minimal points are a concrete
topological sufficient condition.  The class permits infinitely many
accumulating minimal subsystems and needs neither a clopen decomposition nor
a product-of-cyclic presentation.

## Quantifier and boundary audit

1. The norm in `(FC1)` is the supremum over the starting point `x`; hence a
   maximizing sequence gives empirical measures whose `f`-integrals retain
   the limsup.  Comparing with every invariant measure upgrades the limsup to
   the exact limit formula `(FC0)`.
2. Translation of a box changes only a Følner boundary, so every weak-star
   cluster measure is invariant.  No generic-point or ergodic theorem is
   assumed.
3. One measure is constructed for each basis function.  The countable convex
   mixture, rather than any individual measure, is what guarantees full
   support.
4. On a minimal subsystem, the support of any invariant probability is all
   of that subsystem.  Amenability supplies existence, while minimality
   supplies faithfulness on the subsystem.
5. The crossed-product trace is faithful because both the coefficient
   measure and canonical conditional expectation are faithful.

## Scope

This does not prove that stable finiteness forces `(FC1)`.  Capacity-zero
open regions can support only unbounded invariant weights, and excluding
them from a stably finite higher-rank crossed product remains the exact
dynamical obstruction.  Thus the theorem enlarges the explicit positive
Problem XI classes and provides a sharp orbit-average test, without claiming
the unrestricted problem.
