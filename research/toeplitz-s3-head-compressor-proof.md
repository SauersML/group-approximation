---
rg: 2
id: toeplitz-s3-head-compressor-proof
kind: route
title: Put permutation matrices on three Toeplitz head coordinates and absorb them into the deep-tail centralizer
target: toeplitz-s3-headed-holonomy-compressor
requires:
  - toeplitz-head-tail-unital-self-embedding
  - toeplitz-finite-head-centralizes-deep-tail
  - parity-headed-compressor-kills-mark-in-exact-matrix-models
---

Put `e=e_(00)+e_(11)+e_(22)`.  The two units

```text
s_0=e_(01)+e_(10)+e_(22)+(1-e),
s_1=e_(00)+e_(12)+e_(21)+(1-e)                           (1)
```

swap the first two and the last two head coordinates respectively and act as
the identity off that three-dimensional head.  Therefore

```text
s_0^2=s_1^2=1,                 (s_0s_1)^3=1,             (2)
```

and they generate a faithful copy of `S_3` in `T^x`.

For every involutive unit `u` in a unital ring, the standard elementary
identity puts `diag(u,u^(-1))=diag(u,u)` in `EL_2`.  Applying it twice gives
`u I_4 in EL_4(T)`.  Hence

```text
c((01))=s_0 I_4,                 c((12))=s_1 I_4          (3)
```

extends to a homomorphism `c:S_3->EL_4(T)`: products of scalar matrices over
the possibly noncommutative coefficient ring multiply in the same order,
`(uI_4)(vI_4)=(uv)I_4`.  Faithfulness follows from the action on the first
three head coordinates.  Stabilizing by identity blocks embeds the same copy
in every `EL_r(T)` used below.

Every head coefficient commutes with `sigma^N(T)` by `(TFH3)`, so `c(S_3)`
centralizes `beta(Gamma)`.  To compute the intersection, restrict the faithful
unilateral-shift model to the first `N` head coordinates and retain the
elementary matrix coordinate.  An element of `beta(Gamma)` restricts there as

```text
I_N tensor A,                 A in M_r(F_2),              (4)
```

because every tail coefficient acts by its augmentation scalar.  In contrast,
`c(h)` restricts as `P_h tensor I_r`, where `P_h` is the faithful permutation
matrix on the first three head coordinates and the identity on the remaining
head.  Equality in `(4)` would force `P_h` to be scalar.  No nonidentity
element of this `S_3` permutation representation is scalar.  Thus

```text
c(S_3) intersect beta(Gamma)={1}.                         (5)
```

Centralization makes `(TSH3)` a homomorphism; `(5)` and injectivity of
`beta` make it injective.  Its external `S_3` coordinate is trivial, proving
`(TSH4)`.  Universal-lattice property `(T)` for `Gamma`, together with
stability under finite direct products, gives property `(T)` for `Lambda`.
The final exact marked assertion is then precisely the parity-headed
compressor theorem.
