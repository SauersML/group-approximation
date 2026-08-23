---
rg: 2
id: congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits
kind: claim
title: Every congruence Iwahori endpoint fiber contains the full core-commutant conjugacy orbit
distinct_from:
  fixed-packet-correction-retains-multiplicity-gauge: that is the abstract Schur-form gauge for an actuator implementing a packet automorphism; this identifies the gauge concretely in the Iwahori endpoint fiber and proves it can defeat T-commutant alignment even when the congruence group element is unique.
  p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment: that uses two distinct endpoint group elements after the mod-three dilation collapses; this works at every finite congruence level by changing the representation embedding while the group-level Weyl label stays fixed.
  prime-power-iwahori-weyl-endpoint-is-unique-away-from-three: that removes group-element ambiguity; this proves why such uniqueness does not imply representation endpoint uniqueness.
---

Let `G` be a finite congruence quotient carrying the standard square-free
Iwahori elements `(w,r,t)`, and let `K=<r,t>`.  In the left regular
representation `lambda_G`, every unitary

```text
U in lambda_G(K)'
```

produces another exact endpoint over the **same represented core**:

```text
R=lambda(r),       T=lambda(t),
X_0=lambda(w),     X_U=U lambda(w) U^*.                (CCO1)
```

Indeed `Ad(U) o lambda_G` is an exact representation and agrees with
`lambda_G` on `K`.  Thus the endpoint fiber contains the full conjugacy
orbit of `X_0` under the core commutant.

This orbit is not invisible in the relative gauge.  For every standard
`PSL_2(Z/p^k Z)` quotient, one can choose an involution
`U in lambda(K)'` such that

```text
c_U=X_U X_0^(-1)
```

does not commute with `T`, although `X_U` and `X_0` satisfy every Iwahori
row exactly.  Hence prime-power uniqueness of the abstract Weyl element
does not justify arbitrary-baseline `T`-commutant promotion in matrices.

The correct quotient geometry is therefore

```text
exact endpoints over (R,T) / conjugacy by {R,T}' .     (CCO2)
```

A flexible basin theorem must find a nearby point of this entire orbit (or
choose a gauge representative jointly with the repaired core).  It cannot
first freeze the canonical regular Weyl matrix and then try to collapse the
relative gauge to one.

