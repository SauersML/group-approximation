---
rg: 2
id: binary-tracial-two-csp-has-classical-solution
kind: claim
title: Every perfect tracial Boolean unary-binary CSP has a classical solution
distinct_from:
  binary-affine-safe-perfect-support-forces-classical-satisfaction: that treats a general, not necessarily tracial, two-player commuting strategy under an affine-safety hypothesis on its positive edge supports; this uses faithful tracial operator-zero semantics and allows every Boolean unary or binary relation, including the nonlinear three-of-four fiber.
  bounded-width-operator-csp-no-gap: that imports the general bounded-width classification; this gives a self-contained implication-graph proof for the exact Boolean unary-binary case.
  perfect-commuting-unique-game-is-classically-satisfiable: that handles arbitrary answer alphabets under unique constraints by vector transport; this handles every Boolean unary or binary relation by projection order.
---

**ESTABLISHED BINARY TRACIAL COLLAPSE.**  Let `I` be a finite Boolean CSP
whose constraints are arbitrary unary or binary relations.  Suppose `I` has
an exact operator solution in a finite tracial von Neumann algebra: every
Boolean variable `x` is represented by complementary projections

```text
P_x^0+P_x^1=1,       P_x^0 P_x^1=0,
```

the endpoint PVMs commute inside every binary constraint, and every forbidden
joint atom is zero.  Then `I` has a deterministic classical solution.  The
same conclusion holds when the data initially come from a perfect tracial
correlation: after passing to the faithful support of its GNS representation,
zero tracial loss makes every forbidden joint projection zero.

Consequently no perfect-tracial-versus-finite-dimensional gap can be compiled
using only Boolean unary and binary predicates.  This includes the unique
minimal nonlinear Boolean edge

```text
F_2^2 minus {g}.
```

That three-of-four fiber may occur with all three atoms of positive trace,
but it is only a local witness of nonlinear support, not a complete gap
source: the whole unary-binary instance still has a one-dimensional perfect
model.

The tracial/operator-zero scope is load-bearing.  In a general nonsynchronous
commuting strategy, a forbidden product may annihilate only the distinguished
state vector.  Same-player projections encountered along an implication path
need not commute, so the projection-order proof below does not apply without
a tracial reduction or another operator-zero hypothesis.

For groupification this leaves a sharp residue.  A direct marked-sector word
cannot prune one character from two commuting Boolean selectors by
`central-selector-spectra-cannot-prune-a-nonlinear-predicate`.  A selected
primitive corner can realize the three atoms locally, as in
`s4-standard-corner-realizes-shared-nand-chord`, but finite networks of those
packets remain matricial by
`finite-sheet-transport-networks-are-exactly-matricial`.  Thus the minimal
fiber does not bypass the common-corner/nontransport compiler problem.
