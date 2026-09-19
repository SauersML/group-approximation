---
rg: 2
id: one-product-holonomy-countermodel
kind: route
title: Alternate a periodic clock mismatch with its inverse conjugate
target: one-product-holonomy-does-not-sew-four-bs-clocks
requires:
  - periodic-bs-clock-defeats-spectral-first-hit-checksum
---

Use the periodic clock `Z=Z_q` and doubling permutation `P=P_q`.  Put

```text
C=Z^2P=PZ.
```

Because the diagonal factor commutes with `Z`,

```text
C Z C^(-1)=Z^2,
CZ^(-1)=P.                                            (OHC1)
```

Every permutation is conjugate to its inverse: reverse each cycle of the
permutation underlying `P`.  Let `R` be the resulting permutation unitary,
so

```text
RPR^*=P^(-1).
```

Set

```text
T=RZR^*,
D=RCR^*.
```

Conjugating `(OHC1)` gives

```text
D T D^(-1)=T^2,
DT^(-1)=P^(-1).                                      (OHC2)
```

Assign `(c_i,z_i)=(C,Z)` for `i=0,2` and `(c_i,z_i)=(D,T)` for
`i=1,3`.  All four Baumslag--Solitar relators are exact, and the left side
of `(OPH1)` is

```text
P P^(-1) P P^(-1)=I.                                (OHC3)
```

Moreover

```text
||C-Z||_2^2=||P-I||_2^2=2-2/q,
||D-T||_2^2=||P^(-1)-I||_2^2=2-2/q.                 (OHC4)
```

For the primes used in `periodic-bs-clock-proof`, `Z`, `P`, and therefore
`T` have Haar limiting moments.  The monomial unitary `C=Z^2P` has the same
property: for every fixed nonzero `k` below the permutation order, the
permutation part of `C^k` is `P^k`, whose only fixed basis vector is `e_0`;
the corresponding diagonal phase is one.  Thus `tr(C^k)=1/q`.  Conjugacy
gives the same statement for `D`.  This proves the claim.

