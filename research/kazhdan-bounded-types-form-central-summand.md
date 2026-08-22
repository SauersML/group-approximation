---
rg: 2
id: kazhdan-bounded-types-form-central-summand
kind: claim
title: Bounded Kazhdan representation types are selected by one finite central C-star summand
distinct_from:
  kazhdan-bounded-unitary-types-are-finite: that is Wang's finiteness theorem; this packages the finite menu into one central projection of the maximal group C-star algebra and computes its trace in every representation.
  commutant-density-forces-bounded-type-mass: that compares multiplicity dimensions; this identifies the bounded-type mass appearing there with one scalar central-projection moment.
  kazhdan-projection-finite-target-calculus: that concerns the projection onto invariant vectors for the trivial type; this simultaneously selects every irreducible type up to an arbitrary fixed degree.
---

Let `Gamma` be an infinite discrete property-`(T)` group and fix `K`.  There
is a central projection

```text
p_<=K in C*_max(Gamma)                                    (KCS1)
```

such that, for every finite-dimensional representation
`rho:Gamma->U(H)`, `rho(p_<=K)` is exactly the projection onto the sum of
all irreducible subrepresentations of degree at most `K`.  In the notation
of `commutant-density-forces-bounded-type-mass`,

```text
tr_H(rho(p_<=K))=mu_K.                                    (KCS2)
```

The regular representation kills this projection:

```text
lambda_Gamma(p_<=K)=0,       tau_Gamma(p_<=K)=0.          (KCS3)
```

Consequently the exact calibration of the parity density target can be
made scalar.  For the finite constant `r_K` from Wang's theorem,

```text
tr(rho(p_<=K))^2/(K^2 r_K)
 <= dim End_Gamma(H)/dim(H)^2
 <= tr(rho(p_<=K))^2+1/(K+1)^2.                          (KCS4)
```

Thus forcing positive old commutant density is equivalent, up to choosing a
fixed cutoff, to forcing positive trace of one canonical central projection.
Since `(KCS3)` makes every fixed group-algebra approximation to that
projection canonical-trace null, this does not by itself prove `(PCD1)`; it
identifies its precise scalar trace-promotion content.  A proposed
coefficient cell may be tested by whether forbidden Schur mass forces the
`p_<=K` moment.  Merely making the local Reynolds carrier invariant is not
enough.

