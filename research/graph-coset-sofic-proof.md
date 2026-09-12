---
rg: 2
id: graph-coset-sofic-proof
kind: route
title: Separate a graph element in a finite quotient of the target factor
target: graph-coset-mixed-module-is-sofic
requires: []
---

Take `(g,h) in Gamma x H` outside `L_phi`, so `h != phi(g)`.  Residual
finiteness of `H` supplies a finite quotient `q:H -> Q` with
`q(h) != q(phi(g))`.  The homomorphism

```text
Psi: Gamma x H -> Q x Q,
Psi(a,b)=(q(phi(a)),q(b))
```

sends `L_phi` into the diagonal of `Q x Q`, while `Psi(g,h)` lies outside
that diagonal.  Thus every point outside `L_phi` is separated from it by a
finite quotient, proving subgroup separability.

For the general form, injectivity of `pr_Gamma|L` writes

```text
L={(p,phi(p)):p in P},  P=pr_Gamma(L).
```

Because `L` is finitely generated, so is `P`.  Given `(g,h) notin L`, if
`g notin P`, LERF for `Gamma` gives a finite quotient whose image of `g` is
outside the image of `P`; composing with the first projection separates the
point from `L`.  If `g in P`, then `h != phi(g)` and the preceding residual-
finiteness argument in `H` separates them.  Hence this more general `L` is
also separable.

For completeness, separability directly gives the finite Schreier models.
Given a finite window of cosets, choose representatives and intersect the
finitely many finite quotients needed to preserve every inequality
`a_i^(-1)a_j notin L_phi` visible in that window (and after multiplication by
the finite test set).  The action on the resulting finite quotient coset
space reproduces all equalities and inequalities in the window exactly.
Therefore `Lambda curvearrowright Lambda/L_phi` is a sofic action.

The group `Lambda` is sofic because direct products of sofic groups are
sofic.  Gao--Kunnawalkam Elayavalli--Patchell, Theorem 3.6 in
[*Soficity for group actions on sets and applications*](https://arxiv.org/abs/2401.04945),
then says that a finite-lamp generalized wreath product over a sofic action
of a sofic actor is sofic, proving `(GCM1)`.
