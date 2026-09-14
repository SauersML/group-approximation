---
rg: 2
id: simple-kazhdan-group-gives-property-t-factor-in-r-omega
kind: claim
title: The simple Kazhdan LEF subshift group has a property (T) II_1 factor that embeds in R^omega
---
For an infinite minimal subshift `X`, the group `G_X = EL_3(LC(X,F_2) ⋊_T Z)` has a
separable II_1 group factor `L(G_X)` with property (T) that embeds as a von Neumann
subalgebra of the ultrapower `R^ω` of the hyperfinite II_1 factor. See
`simple-kazhdan-group-gives-property-t-factor-in-r-omega-proof`.

This bears on Brown's von Neumann formulation of the question: embed the group in the
unitary group of an R^ω-embeddable McDuff factor. McDuff factors are separable, so the
witness is `L(G_X) ⊗̄ R`, not `R^ω`. See `brown-mcduff-witness-for-simple-kazhdan-lef-group`,
which also shows that the hyperfinite factor `R` cannot serve.

Repair (2026-09-13, sk-operator-algebras): the earlier text justified Brown's form by
"`R^ω` is McDuff", but `R^ω` is non-separable and outside McDuff's setting.

A property (T) R^ω-embeddable II_1 factor is not itself new (e.g. `L(SL_3(Z))`). The
only new element is that it is the group factor of an infinite simple group.
