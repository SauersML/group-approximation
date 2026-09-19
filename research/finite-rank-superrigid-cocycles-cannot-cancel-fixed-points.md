---
rg: 2
id: finite-rank-superrigid-cocycles-cannot-cancel-fixed-points
kind: claim
title: Finite-rank superrigid cocycles cannot cancel fixed points of a torsion-free actor
distinct_from:
  finite-permutation-cocycles-cannot-cancel-infinite-isotropy: that uses positivity and almost-surely infinite stabilizers to exclude finite permutation packets; this allows arbitrary unitary phases but assumes that the cocycle is cohomologous to a homomorphism.
  relation-cocycles-preserve-full-group-rectangles: that forces identity holonomy on fixed points for cocycles descending to the principal relation; this allows nontrivial isotropy holonomy and rules it out by a power-trace obstruction.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that concerns preservation of an already Haar-algebraic crossed-product inclusion under coinduction; this rules out using cocycle-superrigid coinduction to manufacture regular finite-rank decorated normalizers.
---

Let a torsion-free countable group `Gamma` act pmp on `(X,mu)`, let
`R` be its orbit relation, and suppose that the action is not essentially
free. Fix `n>=1`. If

```text
b in Z^1(Gamma curvearrowright X,U(n))
```

is cohomologous to a homomorphism `pi:Gamma->U(n)`, then the decorated
normalizers

```text
v_g=b_g(u_g tensor 1_n)                                (SRC1)
```

do not have the regular character. In fact there are `g!=e` and
`1<=k<=n` such that

```text
(tr_n tensor tau_R)(v_(g^k))
 =mu(Fix(g^k)) tr_n(pi(g)^k) !=0.                       (SRC2)
```

Therefore a finite-rank isotropy-cancellation construction for a
torsion-free nonfree action must use a cocycle that is not cohomologous to
any finite-dimensional homomorphism.

This excludes the standard property-`(T)` Bernoulli and coinduced repair
under the usual cocycle-superrigidity hypotheses. Popa's and Drimbe's
`U_fin` cocycle-superrigidity theorems make every `U(n)`-valued cocycle
in their respective settings cohomologous to a homomorphism; on a
torsion-free nonfree actor `(SRC2)` then blocks regular trace. Diffuse
scalar cancellation is possible only outside this superrigid regime.
