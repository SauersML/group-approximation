---
rg: 2
id: manzoor-haar-cylinder-audit-proof
kind: route
title: Expand the IRS correlation and trace every existential choice in the separation proof
target: manzoor-separation-does-not-specify-haar-cylinders
requires: []
---

For each question `x`, the same-question involutions commute, so

```text
e_x^a = product_(i<=m) (1+(-1)^(a_i)u_(x,i))/2
      = 2^(-m) sum_(I subset [m])
          (-1)^(sum_(i in I)a_i) u_(x,I).
```

Substitute this and the analogous expansion for `e_y^b` into Manzoor's
definition

```text
p(a,b|x,y)=tau_H((1-J)e_x^a e_y^b).
```

Since `tau_H(w)=Pr[w in H]`, distributing `(1-J)` gives `(MHC2)`.  Every term
is a marginal event for one group word.  No intersection of two distinct
membership events occurs.  This agrees with Manzoor's Section 3.2 statement
that the value is a finite linear combination of probabilities
`Pr[g in H]` for words of bounded length.

Definition 3.11 imposes precisely `(MHC4)` (together with the same conditions
on every required generator).  These values are `0` and `1= p^0`; hence they
do not violate the necessary Haar-linear fixed-cylinder law.  Probability
one is preserved under finite intersection, so combining the displayed
relators gives no new value.

Theorem 3.13 assumes for contradiction that no IRS/quantum separation exists
and constructs a halting decider.  Its negation proves existence of a game
but returns no particular Turing machine.  Theorem 3.5 begins by choosing an
IRS strategy whose value lies above `omega*`, again without uniqueness or a
cylinder description.  Finally the proof of Theorems 1.1--1.2 uses closed
convex separation to choose an extreme non-cohyperlinear IRS; it does not
prove that this extreme point is the earlier strategy or preserve any
unlisted cylinder data.  These three existential choices prove the claimed
underdetermination.

For the literal linear-subshift observation, let `z_H(g)=1_(g in H)`.  Every
subgroup contains the identity, so `z_H(e)=1` almost surely.  A closed linear
subshift `K <= F_p^F` contains `0`.  Coordinate evaluation at `e` is a
continuous homomorphism `K -> F_p`; its Haar pushforward is Haar on its image,
so it is either the point mass at `0` or uniform on a nonzero finite subgroup.
It cannot be the point mass at `1`.  This rules out literal equality of the
indicator law with linear Haar measure, but says nothing about a nonlinear
stabilizer map or measurable factor, exactly as stated.
