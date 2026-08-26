---
rg: 2
id: free-lamp-sofic-class-action-proof
kind: route
title: Restrict charts to a finite set of basis elements; extend set-charts to a free group on the chart set
target: free-lamp-sofic-class-action-is-sofic-set-action
requires: []
---

Notation (Alekseev--Bradford Definition 4.23).  `alpha : G -> Aut(Delta)`,
`Delta = F(X)`; a function `phi : G -> Sym(A)`, `A` finite, is an
`(F, E, epsilon, Lambda)`-automorphic approximation of `alpha` if there are
`S subseteq A` with `|S| > (1 - epsilon)|A|` and injective partial
homomorphisms `pi_s : E -> Lambda` (`s in S`) with
`pi_(phi(g) s)(h) = pi_s(alpha(g)^(-1)[h])` whenever `g in F`, `h in E`,
`phi(g) s in S`, `alpha(g)^(-1)[h] in E`.  The action is a sofic `C`-action
if such approximations exist with `Lambda in C` for every `(F, E, epsilon)`.
Definition 4.16 (sofic action on a set) is the same statement with `E` a
finite subset of `X`, `B` a finite set in place of `Lambda`, and injective
functions `pi_s : E -> B`.

**Automorphic approximation implies orbit approximation.**  Given finite
`F subseteq G`, `X_0 subseteq X` and `epsilon`, take `E = X_0 subseteq F(X)`
(basis elements are elements of `Delta`) and an `(F, E, epsilon, Lambda)`-
automorphic approximation.  Each `pi_s` is injective on `E = X_0`, and for
`x in X_0` with `alpha(g)^(-1)[x] = g^(-1) x in X_0` the equivariance reads
`pi_(phi(g)s)(x) = pi_s(g^(-1) x)`.  Let `B = union_(s in S) pi_s(X_0)`, a
finite subset of `Lambda`.  Then `(pi_s : X_0 -> B)` is an
`(F, X_0, epsilon)`-orbit approximation of the set action, with the same
`A`, `phi`, `S`.  Hence the set action is sofic.

**Orbit approximation implies automorphic approximation.**  Given finite
`F subseteq G`, `E subseteq F(X)` and `epsilon`, let `X_0 subseteq X` be the
finite set of basis elements occurring in the reduced words of `E` and of
`alpha(g)^(-1)[E]`, `g in F`.  Take an `(F, X_0, epsilon)`-orbit
approximation with charts `pi_s : X_0 -> B`, `B` finite, and put
`Lambda = F(B)`, the free group on `B`, which lies in `C`.  Extend `pi_s`
to the homomorphism `F(X_0) -> F(B)` sending each basis element to the
basis element `pi_s(x)`; it is injective (an injective map of bases induces
an injective homomorphism of free groups), and its restriction to `E` is an
injective partial homomorphism.  Equivariance on basis elements gives
`pi_(phi(g)s)(alpha(g)[x]) = pi_s(x)` for `x, gx in X_0`, and both sides of
`pi_(phi(g)s)(h) = pi_s(alpha(g)^(-1)[h])` are products of such basis
values, so it holds for every `h in E` with `alpha(g)^(-1)[h] in E`.  Hence
the automorphism action is a sofic `C`-action.

**The Kun--Thom instance.**  Corollary D of Kun--Thom says the coset action
`G -> Sym(G/Gamma)` is not sofic (`coordinate-action-not-sofic`), so by the
first direction the free-lamp action is not a sofic `C`-action for any `C`
containing free groups, in particular not a sofic hyperlinear action.
