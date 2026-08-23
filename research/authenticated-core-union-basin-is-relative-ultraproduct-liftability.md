---
rg: 2
id: authenticated-core-union-basin-is-relative-ultraproduct-liftability
kind: claim
title: Retraction to the union of endpoint fibers is exactly relative ultraproduct liftability
distinct_from:
  regular-iwahori-relative-congruence-exactification: that is the open arithmetic correction theorem; this gives its exact authenticated-core ultraproduct normal form and separates what Selberg does after a lift from the lift itself.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies and metrizes the exact zero set at every finite level; this proves that retraction to the union of those zero sets is an additional lifting property.
  bs14-thresholded-newton-needs-coordinate-basin: that states the mixed-norm local Newton theorem and its missing coordinate basin; this identifies that global basin with a relative lift of an ultraproduct homomorphism.
  exact-torsion-frame-has-rank-one-strict-counterpackets: that refutes same-dimensional lifting with a concrete boundary compression; this incorporates that example and leaves precisely the flexible lift.
---

Let `Q_n` be moving odd congruence quotients, let

```text
beta_n:K -> U(d_n)                                       (AUL1)
```

be exact authenticated BS-core representations, and let `X_n` have all
four square-free relative defects tending to zero.  In the tracial matrix
ultraproduct, the classes of `(X_n,beta_n)` define an exact homomorphism

```text
Pi:A=PSL_2(Z[1/2]) -> product_omega M_(d_n)              (AUL2)
```

extending the prescribed core embedding `[beta_n]`.

Retraction of `X_n` to the **union** of all exact endpoint orbits over
`beta_n`, with `o(d_n)` flexible padding allowed, is equivalent to the
following relative liftability statement for `(AUL2)`:

> after passing to the representing sequence, there are exact
> finite-dimensional congruence representations `pi_n` on dimensions
> `D_n=d_n+o(d_n)` and almost-full isometries whose compressed generator
> tuples converge in normalized HS to `(X_n,beta_n)`.

At a fixed level and dimension, the possible lift types are exactly the
nonnegative restriction-ring fiber

```text
F_(beta_n)={m>=0:res_(Q_n)^K(m)=[beta_n]},              (AUL3)
```

by `congruence-endpoint-orbits-are-restriction-ring-fibers`.  Once a type
`m_n` and a lift have been produced, the uniform Selberg gap controls the
normal distance to its core-commutant orbit.  It does **not** produce
`m_n` or the coordinate lift from the exact ultraproduct homomorphism.

This distinction is sharp.  Cuspidal restriction-kernel moves show that no
preferred fiber point can be selected from the core or the limiting
character.  Compressed even-Weil packets show that a lift can require an
extra boundary dimension even when every residual tends to zero; hence the
same-dimensional version is false.  Their one-line completion is compatible
with the flexible formulation and does not refute it.

Therefore uniform Selberg normal coercivity plus compactness of each finite
fiber does not prove the global union-basin theorem.  A failed flexible
union-basin sequence is precisely a non-liftable relative ultraproduct
extension `(AUL2)`.  Excluding such extensions, or reconstructing their
energy-controlled boundary carriers, is the remaining arithmetic theorem.

