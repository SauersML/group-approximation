---
rg: 2
id: every-finitely-presented-torsion-group-is-finite
kind: claim
title: Every finitely presented group in which every element has finite order is finite
distinct_from:
  there-is-a-finitely-presented-infinite-torsion-group: that is the negation of this claim; exactly one of the two holds, and the Problem 1.11 root is established by whichever does.
---

**OPEN.** If a group `Q` has a finite presentation and every element of `Q`
has finite order, then `Q` is finite.

This is the nonexistence answer to Zaremsky Problem 1.11
(`zaremsky-1-11-fp-infinite-torsion-group`). Groups of type F∞ are finitely
presented, so it would also rule out infinite torsion groups of type F∞.

## Fences proved around it (necessary conditions, not answers)

- `fp-torsion-group-is-no-limit-of-non-torsion-groups`, via
  `fp-direct-limit-of-surjections-stabilizes`: a finitely presented torsion
  group is torsion at a finite stage of every sequence of quotients of a
  finitely generated group converging to it. A construction that kills
  infinite-order elements in infinitely many steps, with infinitely many
  stages still containing elements of infinite order, never ends at a
  finitely presented group.
- `fp-torsion-presentations-have-positive-orbifold-char`: take a finite
  presentation `<X | R>` of a torsion group, with relators `r = u_r^(n_r)` and
  roots `u_r` not proper powers. Every finite quotient `Q` satisfies
  `1 - |X| + sum_r 1/o_Q(u_r) >= 1/|Q|`. For residually finite groups the
  inequality holds strictly with the orders taken in the group.

## Attempts

- Known special classes, where the conclusion holds for class-specific
  reasons: linear groups (Burnside–Schur), hyperbolic groups (infinite ones
  contain elements of infinite order), and residually finite groups of
  bounded exponent (restricted Burnside problem). None of these arguments uses
  finite presentability, so none extends. The obstruction lane
  z1-11-torsion-block owns this side.
- Quotients of finitely presented torsion-by-cyclic groups: finite whenever
  the torsion base is just-infinite, by the construction lane's coinvariant
  analysis. This is a statement about one family of candidates, not a proof
  of this claim.
- Finite-presentation-specific mechanisms (obstruction lane, 2026-09-13). The
  mechanisms that actually use finitely many relators are:
  - stabilization of limits (the limit fence above);
  - relator counts in finite-index subgroups (the orbifold-characteristic
    fence above);
  - gap theorems for Dehn functions: a subquadratic Dehn function forces
    hyperbolicity, so an infinite finitely presented torsion group has at
    least quadratic Dehn function. That import has not been re-read.
  Each one only excludes subclasses. Where it dies: none turns "finitely many
  relators" plus "every element has finite order" into finiteness when the
  presentation has positive orbifold characteristic and the group is not a
  limit of non-torsion stages.
- Open crux for a counterexample: a *finite* set of power relators whose group
  is already torsion and whose orbifold characteristic is positive, or which
  is not residually finite. An example would be a finite Golod–Shafarevich
  presentation with many deep `p`-th power relators. Nothing above excludes
  that shape. The Golod–Shafarevich inequality `1 - |X| t + sum_r t^(deg r) < 0`
  and `sum_r 1/o(u_r) > |X| - 1` hold simultaneously when there are many
  relators `u^p` with `u` deep in the Zassenhaus filtration.
