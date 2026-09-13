---
rg: 2
id: stw29-separative-projection-monoid-dichotomy
kind: claim
title: Simple algebras with property (SP) and separative projection monoid, in particular limits of separative building blocks, are stably finite or purely infinite
distinct_from:
  stw29-projection-qq-characterizes-rr0-dichotomy: that gives almost unperforation of V(A) as a sufficient condition under real rank zero; this gives separativity of V(A), a cancellation-type condition that passes to inductive limits of arbitrary building blocks, and needs only property (SP).
  stw99-problem-lx-rr0-weak-cancellation: that problem asks whether all real rank zero algebras are separative; this is the unconditional theorem that separativity of V(A), however obtained, gives the dichotomy for simple A with property (SP).
---

**Theorem.**  Let `A` be a simple C\*-algebra.

1. If `A` contains a nonzero finite projection and some matrix algebra over
   `A` contains an infinite projection, then `V(A)` is not separative.  An
   explicit witness is `2x = 2y = x + y` with `x != y`.  No real rank or (SP)
   hypothesis is needed.
2. Hence, if `A` has property (SP) (for example real rank zero) and `V(A)` is
   separative, then `A` is stably finite or purely infinite.  For simple
   algebras, separativity of `V(A)` is the same as weak cancellation.

Separativity of `V(A)` holds in each of the following cases.

* `V(A)` is tame, i.e. an inductive limit of finitely generated refinement
  monoids (Ara--Goodearl).  This covers finitely generated `V(A)`, graph
  monoids, and primely generated or regular (`2x <= x`) conical refinement
  monoids.
* `A = lim (A_n, phi_n)` with arbitrary connecting \*-homomorphisms and every
  `V(A_n)` separative, with no real rank, simplicity or unitality assumption on
  the `A_n`.  Separative building blocks include C\*-algebras of stable rank
  one, purely infinite simple C\*-algebras, `C(X) tensor O_infinity` for
  compact connected `X`, finite direct sums of these, and algebras with tame
  `V`.

**Consequences.**
* A counterexample to Problem XXIX presented as an inductive limit must
  have non-separative `V(A_n)` at cofinally many stages.  Blocks of the form
  stable rank one plus purely infinite simple can never produce one, whatever
  the connecting maps.
* Rordam's building blocks `M(C(Z, K))` over `Z = product of S^2` are
  necessarily non-separative.  His limit `B` is simple with a finite and an
  infinite projection, so part 1 applies to `B`, and separativity would pass to
  the limit.  This agrees with part 1: his algebras have property (SP) but are
  not of real rank zero (`rordam-mixed-examples-not-real-rank-zero`).
