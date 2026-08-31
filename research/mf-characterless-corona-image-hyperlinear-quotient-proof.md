---
rg: 2
id: mf-characterless-corona-image-hyperlinear-quotient-proof
kind: route
title: Push a norm-corona embedding to one tracial ultraproduct and identify its kernel
target: mf-characterless-corona-image-has-hyperlinear-quotient
requires: []
artifacts:
  - research/artifacts/approximation-recognition-roots-audit-2026-08-31.md
---

Fix a free ultrafilter `omega`.  Normalized matrix traces define a tracial
state on the norm corona,

```text
tau_omega([(x_n)]) = lim_omega tr_(d_n)(x_n),
```

because norm-null sequences are normalized-Hilbert--Schmidt-null.  Equivalently
there is a canonical unital homomorphism

```text
q_omega: Q -> product_omega^(2) M_(d_n).
```

Let

```text
N_omega = ker(q_omega compose u) normal G.
```

Then `G/N_omega` embeds into a matrix tracial ultraproduct, so it is
hyperlinear.  It remains only to prove that `N_omega != G`.

Suppose instead that `N_omega=G`.  Then
`q_omega(u(g))=1` for every `g`.  Since the unitaries `u(g)` generate `A`,

```text
q_omega(A) = C 1.
```

Consequently `q_omega|_A`, read as a map `A->C`, is a unital
*-homomorphism sending every `u(g)` to `1`: it is exactly a character of `A`
extending augmentation.  This contradicts the hypothesis.
Therefore `N_omega` is proper and the quotient is nontrivial.

If `G` is nonabelian simple, a proper normal subgroup is trivial, so
`q_omega compose u` itself is injective and `G` is hyperlinear.  Conversely,
for a nonhyperlinear nonabelian simple weak-MF group augmentation must factor
through every corona image algebra.  QED.
