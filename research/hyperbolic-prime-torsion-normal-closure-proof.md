---
rg: 2
id: hyperbolic-prime-torsion-normal-closure-proof
kind: route
title: Pass to a prime-order power and classify its normal closure
target: hyperbolic-prime-torsion-residual-dichotomy
requires:
  - finite-torsion-carrier-virtual-torsionfree-criterion
---

An element of finite order `m>1` has a power of prime order: if `p` divides
`m`, then a suitable power has order `p`.  Since `R` is a subgroup, it is
torsion-free exactly when it has no nonidentity prime-order element.

A hyperbolic group has finitely many conjugacy classes of finite subgroups,
so it has finitely many conjugacy classes of prime-order subgroups.  Every
prime-order subgroup is conjugate to one of `P_1,...,P_s`.  Normality of `R`
therefore gives

```text
R has no prime torsion  iff  R intersect P_j={1} for every j.
```

If the intersections are trivial, each of the finitely many nonidentity
generators of the `P_j` survives in some finite quotient by the definition
of `R`.  Taking the diagonal product of those quotients gives one finite
quotient which is nontrivial, hence injective, on every prime-order `P_j`.
Its kernel contains no torsion: a hypothetical torsion element has a
prime-order power, conjugate into some `P_j`, and normality of the kernel
would contradict injectivity there.  Conversely, the kernel of any such
quotient is a finite-index torsion-free subgroup.  This proves the four
equivalences (and is the prime-order sharpening of the finite-carrier test).

Now suppose `x in R` has prime order and put `N=normal_closure_G(x)`.  The
finite residual is characteristic, hence normal, so `N subset R`.

If `N` is finite, maximality of the finite radical gives `N subset E` and
thus `x in E`.  Conjugation on `E` is a homomorphism

```text
G -> Aut(E)
```

with finite target.  Every element of `R`, including `x`, lies in its
kernel.  Hence `x` centralizes `E`, proving `x in R intersect Z(E)`.

Suppose instead that `N` is infinite.  A standard boundary fact for
non-elementary hyperbolic groups says that every infinite normal subgroup
has full limit set.  It cannot be virtually cyclic: an infinite elementary
normal subgroup would have a finite invariant limit set, whereas normality
would make that set invariant under the non-elementary group `G`.  Thus `N`
is non-elementary and its limit set is `boundary(G)`.  The usual ping-pong
argument for two independent loxodromic elements gives a nonabelian free
subgroup of `N`.  Since `N subset R`, the same conclusions hold for `R`.

If `E={1}`, the finite alternative is impossible.  Hence every nontrivial
torsion obstruction forces the non-elementary alternative.  More generally,
an elementary or amenable subgroup of a hyperbolic group contains no
nonabelian free subgroup; if such a subgroup is also normal in a
non-elementary hyperbolic group, it must be finite.  With `E={1}` it is
therefore trivial.  Applying this to `R` proves the final sufficient
criteria.
