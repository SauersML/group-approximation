---
rg: 2
id: amenable-fp-not-re-from-unbounded-folner-functions
kind: route
title: A recursively enumerable amenable locus would carry one recursive Følner bound
target: amenable-finite-presentations-are-not-recursively-enumerable
requires: [folner-functions-of-fp-amenable-groups-have-no-recursive-bound, recursive-amenable-classes-have-uniform-folner-bounds]
---

Suppose `AMENABLE_fp` is recursively enumerable. Finite presentations are
finitely generated recursive presentations, so the class `C = AMENABLE_fp` meets
the hypothesis of Corollary 3.6 in
`recursive-amenable-classes-have-uniform-folner-bounds`. It supplies a recursive
`U_C` with `F_(Γ,X) <= U_C` eventually, for every finite presentation `<X | R>`
of an amenable group, with the generating set of the presentation.

That contradicts `folner-functions-of-fp-amenable-groups-have-no-recursive-bound`
applied to `U = U_C`. `∎`

This route is independent of any reduction. A negative answer to Gromov's
question would already place `AMENABLE_fp` outside `Sigma^0_1`.
