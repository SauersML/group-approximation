---
rg: 2
id: kazhdan-images-in-haagerup-algebras-are-atomic
kind: claim
title: A Kazhdan group's image in a Haagerup finite von Neumann algebra generates a purely atomic algebra
distinct_from:
  invariant-size-collapse: that is the principle that a conjugation-invariant monotone size forbids strict compression; this is an approximation-free rigidity statement about which algebras a Kazhdan group can generate, with no compressor in it.
  commutant-no-growth: that counts the linear dimension of a genuine finite-dimensional representation; this proves that a Kazhdan image inside any Haagerup finite von Neumann algebra already decomposes into finite-dimensional representations, with no dimension given in advance.
---

**ESTABLISHED.** Let `Lambda` be a countable group with property (T), let
`(M,tau)` be a finite von Neumann algebra with faithful normal tracial state,
and let `sigma : Lambda -> U(M)` be a homomorphism. Put `B = sigma(Lambda)''`.
If `B` has the Haagerup property, then

```text
B = directSum_k M_(n_k)(C),     n_k finite,                      (KHA1)
```

so the left action of `sigma(Lambda)` on `L^2(M)` is a direct sum of
finite-dimensional representations.

The hypothesis holds whenever `M` is amenable: `B` is the image of a trace
preserving conditional expectation, hence injective, and it has separable
predual because `Lambda` is countable, so `B` is hyperfinite. It also holds
when `M` has separable predual and the Haagerup property, since that property
passes to von Neumann subalgebras (compress the deformation by `E_B`). Free
group factors, amalgamated free products of amenable algebras over amenable
subalgebras, and hyperfinite algebras are therefore all covered.

No approximation, trace condition on `sigma`, or compressor enters. This is
the standard rigidity-versus-compact-deformation mechanism, recorded here with
a complete proof because the downstream wall obstruction
`haagerup-targets-carry-no-relative-wall` consumes exactly `(KHA1)`.

DERIVATION
kazhdan-haagerup-atomic-image-proof
