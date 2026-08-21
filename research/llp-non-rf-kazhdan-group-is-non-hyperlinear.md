---
rg: 2
id: llp-non-rf-kazhdan-group-is-non-hyperlinear
kind: claim
title: A non-residually-finite Kazhdan group whose full C*-algebra has the local lifting property is not hyperlinear
distinct_from:
  non-rf-kazhdan-weak-ucp-iff-non-hyperlinear: that is the equivalence of weak ucp-stability with non-hyperlinearity for non-RF Kazhdan groups; this feeds it a C*-algebraic SUFFICIENT condition for weak ucp-stability, Kirchberg's LLP, and records that LLP passes to subgroups so the Ioana--Spaas--Wiersma failures fence the candidates.
  hs-stability-plus-fd-residual-forces-nonhyperlinearity: that consumes a stability hypothesis of the group; this consumes a lifting property of its full C*-algebra, a hypothesis of a different type that operator-algebraic permanence theorems can address.
  thom-central-corner-criterion: that is Thom's criterion for hyperlinearity of central extensions through twisted group algebras, used for the Clifford lamp group; this is a non-hyperlinearity criterion through Kirchberg's LLP for Kazhdan groups.
---

**THEOREM.**  Let `Gamma` be a finitely generated group with Kazhdan's
property (T) that is not residually finite, and suppose the full group
C*-algebra `C^*(Gamma)` has Kirchberg's local lifting property (LLP).
Then `Gamma` is not hyperlinear.

Equivalently, **every non-residually-finite Kazhdan group is either
non-hyperlinear or a counterexample to LLP for full group C*-algebras.**
Before Ioana--Spaas--Wiersma (GAFA 30 (2020), arXiv:2006.01874) no group
C*-algebra was known to fail LLP; their examples are `SL_n(Z)` (`n >= 3`)
and `Z^2 rtimes SL_2(Z)`, obtained from second cohomology, and by this
theorem Thom's hyperlinear Kazhdan groups without the factorization
property are further (non-cohomological) LLP failures.

**Mechanism.**  LLP of `C^*(Gamma)` implies weak ucp-stability of `Gamma`
(Ioana--Spaas--Wiersma Cor. 1.7 as quoted by Dogon arXiv:2211.10492 p. 4;
directly: a hyperlinear approximation is a *-homomorphism of `C^*(Gamma)`
into a tracial matrix ultraproduct, which is a quotient of the bounded
product `prod M_(d_n)`; LLP lifts it ucp on every finite-dimensional
operator system `span(F)`, Arveson extends the lift to `C^*(Gamma)`, and
Stinespring dilates the components to genuine representations whose
corners agree with the approximation on `F`).  Then
`non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` gives non-hyperlinearity.

**LLP passes to subgroups.**  For `H <= Gamma` the conditional expectation
`E : C^*(Gamma) -> C^*(H)` is ucp, so `E (x) id` is defined on maximal
tensor products and `C^*(H) (x)_max B -> C^*(Gamma) (x)_max B` is injective;
with Kirchberg's characterization `LLP <=> (x)_max B(l^2) = (x)_min B(l^2)`
one gets `LLP(C^*(Gamma)) => LLP(C^*(H))`.  Hence a candidate `Gamma` for
`non-rf-kazhdan-group-with-llp-full-c-star-algebra` must contain no
subgroup known to fail LLP: no `SL_n(Z)` (`n >= 3`), no `Z^2 rtimes SL_2(Z)`,
and more generally no relative-(T) pair with the Ioana--Spaas--Wiersma
second-cohomology obstruction.
