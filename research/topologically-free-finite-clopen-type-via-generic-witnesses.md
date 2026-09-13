---
rg: 2
id: topologically-free-finite-clopen-type-via-generic-witnesses
kind: route
title: Apply the topologically free realization to a countable part of the Ortega-Perera-Rordam monoid
target: topologically-free-minimal-cantor-action-with-finite-clopen-type
requires: [refinement-monoids-are-topologically-free-cantor-types, opr-mixed-simple-refinement-monoid]
---

**Credit.**  This is an independent later proof.  Priority belongs to
Boldrini--Prasad (`topologically-free-finite-clopen-type-boldrini-prasad-citation`).

**Step 1: a countable mixed monoid.**  Take the countable submonoid
`M' ⊆ M` of the Ortega--Perera--Rordam monoid built in Step 1 of
`measure-free-minimal-cantor-action-with-finite-clopen-type-proof`.
* `M'` is simple, conical and has refinement.
* It contains `u` and `w` with `2u + 2u + w = 2u`, and `u` is finite in `M'`.
* `M' != {0}`, and `M'` is not `Z^+`.

**Step 2: realization.**  By `refinement-monoids-are-topologically-free-cantor-types`
there is a minimal, topologically free action of `F_infinity` on the Cantor
space `X` with `(S(X, F_infinity), [1_X]) ≅ (M', u)`.

**Step 3: verification.**
* An invariant probability measure would give a state `s` with `s(u) = 1`,
  and then `4 + s(w) = 2`.  So there is none.
* `[1_X] = u` is finite, so `A = X` is the required clopen set.

This is where the attempts recorded on the target claim end.
* The fixed-point obstruction of the non-free realization is avoided by
  choosing the witnesses generically, not by adding clopen sets.
* The Borel/clopen contrast still holds.  With countably many Borel pieces,
  `X` is compressible (Nadkarni).  With finitely many clopen pieces, it is not
  equidecomposable with any proper clopen subset.
