---
rg: 2
id: resolvent-ring-presentation-is-not-faithful-on-r-bar
kind: claim
title: The eight-relator resolvent ring R_l does not present its residually finite model R̄_l, since e x e - e x^q e is nonzero in R_l and zero in R̄_l
distinct_from:
  rf-resolvent-ring-has-z-localized-corner: that constructs the residually finite ring R̄_l as a subring of a product of finite matrix rings; this shows the natural finite presentation R_l maps onto R̄_l with nonzero kernel.
  resolvent-presentation-ring-is-residually-finite: that asks whether R_l itself is residually finite; this only shows R̄_l uses too few finite quotients of R_l.
---

**ESTABLISHED** through `resolvent-ring-presentation-is-not-faithful-on-r-bar-proof`.
Lane proof, not independently reviewed.

**Statement.** Let `l` be a prime and `q != l` a prime. In the finitely presented ring

    R_l = Z<u, x, x', B, e | x x' = x' x = 1, x u = (u+l) x, B(u+1) = (u+1)B = 1,
                           u e = e u = 0, e^2 = e>

the element `δ = e x e - e x^q e` is nonzero. Its image in the ring `R̄_l` of
`rf-resolvent-ring-has-z-localized-corner` is zero. So `R_l -> R̄_l` is not injective.
This answers sub-question 1 of `rf-resolvent-elementary-group-is-fp` negatively.

**What survives.** `R̄_l` uses only the finite modules `M_r`, where the shift `x` has
order `l^(r-1)`. `R_l` has many more finite quotients: shifts of any order in
characteristic `l`, and twisted shifts with a matrix `g` on the vacuum block (see
`resolvent-presentation-ring-is-residually-finite`). So the natural question is
whether `R_l` is residually finite, not whether it presents `R̄_l`.
