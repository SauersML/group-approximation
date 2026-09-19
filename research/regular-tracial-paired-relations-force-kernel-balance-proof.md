---
rg: 2
id: regular-tracial-paired-relations-force-kernel-balance-proof
kind: route
title: The regular trace detects identity after paired conjugacy
target: regular-tracial-paired-relations-force-kernel-balance
requires:
  - regular-paired-finite-group-relations-are-balanced
---

Because the displayed relation holds on generators of `K`, multiplication and
inversion give it for every `k in K`:

```text
pi_1(p_1(k)) = U pi_2(p_2(k)) U^*.
```

Take traces.  By traciality and `(RTK1)`,

```text
p_1(k)=1
 iff tau(pi_1(p_1(k)))=1
 iff tau(pi_2(p_2(k)))=1
 iff p_2(k)=1.
```

Thus `ker p_1=ker p_2`, proving `(RTK3)`.

Apply `regular-paired-finite-group-relations-are-balanced`.  The two finite
regular pullback representations of `K` are unitarily isomorphic.  Hence their
exact intertwiner space contains a unitary at every common amplification.
Every spectral low-energy space contains the zero-energy space, so it too
contains that unitary; a matrix space containing a unitary cannot shrink any
subspace (`U(X)` is already an image of the matrix space with dimension
`dim X`).  Therefore all shrunk-space deficiencies vanish.
