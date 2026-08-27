---
rg: 2
id: sl3-overlap-full-in-fd-ambient-images
kind: claim
title: The integral overlap has the full image in every finite-dimensional ambient SL3 representation
distinct_from:
  sl3-prime-permutation-codensity: that proves the whole integral lattice has the full image in every finite action of the S-arithmetic group; this proves the smaller fixed overlap already has that image and applies it to arbitrary finite-dimensional unitary representations.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that identifies the commutants of the integral and S-arithmetic images; this identifies the image and commutant of the specific finite-index overlap used by denominator conjugacy.
---

Fix a prime `p` and put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),
C_+=C intersect h C h^(-1).
```

For every finite-dimensional unitary representation `sigma:A->U(d)`,

```text
sigma(C_+)=sigma(C)=sigma(A).                           (OFI1)
```

In particular,

```text
sigma(C_+)'=sigma(C)'=sigma(A)'.                       (OFI2)
```

The assertion is uniform in dimension and makes no irreducibility or
multiplicity assumption.  It is the exact overlap-fullness needed to
Kazhdan-round a denominator relative coordinate using only the fixed
conjugacy relations between `C_+` and `h^(-1)C_+h`.

