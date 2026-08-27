---
rg: 2
id: kazhdan-codensity-component-counterexample-proof
kind: route
title: Multiply SL3Z by a simple amenable LEF group
target: kazhdan-codensity-does-not-control-component-actions
requires: []
---

Take `C=SL_3(Z)` and a finitely generated infinite simple amenable LEF group
`D`, and put `A=C times D`.  Both factors are perfect and `C` is normal and
Kazhdan.  Every finite-dimensional unitary representation of `D` is trivial:
a nontrivial one is faithful by simplicity, while a finitely generated
linear group is residually finite, contradicting that infinite simple `D`
has no finite quotients.  Hence every finite-dimensional representation of
`A` has `rho(C)=rho(A)`.

Use separating finite quotients of `C` on sets `X_n` and LEF/sofic models of
`D` on `Y_n`.  The product action on `X_n times Y_n` is a union of uniform
Kazhdan expander components, while `D` moves the component labels.  Since
`A/C=D`, this models the sofic coset action.

Finally, in `L(A)` any noncentral `u in L(D)` commutes with `L(C)` but not
with a chosen noncommuting `h in D`.  The group `A` is sofic, so this is a
Connes-embeddable relative-commutant counterexample satisfying all the exact
hypotheses.
