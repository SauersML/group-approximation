---
rg: 2
id: relator-only-hs-obstruction-has-trivial-model-proof
kind: route
title: Evaluate every presentation word on the identity tuple
target: relator-only-hs-obstruction-has-trivial-model
requires: []
---

For each `d`, send every generator `s in S` to the identity matrix `1_d`.
Evaluation of a group word uses only multiplication and inverse, so every word
in the generators evaluates to `1_d`; in particular every relator does.
Thus every standard normalized-HS presentation defect is exactly zero.

This already proves the logical gate.  A hyperlinear approximation carries
strictly more data than small relator defect: on each prescribed finite set it
also separates distinct group elements (equivalently, for the regular
character formulation, nontrivial words have normalized trace tending to
zero).  The identity tuple deliberately violates that separation while
satisfying all relations perfectly.  Therefore any implication from a
presentation-level obstruction to nonhyperlinearity must use a separation or
trace hypothesis somewhere.

The same observation also distinguishes existence from stability.  A
Fredholm/Bott/rank index may prevent a small-defect tuple from being perturbed
to an exact representation while the tuple itself continues to exist with
arbitrarily small defect.  Since hyperlinearity needs the tuple and not its
repair, an index becomes an existence obstruction only after a separate
estimate converts the marked index density into a positive cost in a quantity
that hyperlinear microstates force to zero.
