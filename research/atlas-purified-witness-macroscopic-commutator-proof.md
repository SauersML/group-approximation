---
rg: 2
id: atlas-purified-witness-macroscopic-commutator-proof
kind: route
title: Threshold the block-monomial commutator gap inside the purified summand
target: atlas-purified-witness-macroscopic-commutator
requires:
  - leavitt-atlas-full-coefficient-purification
  - leavitt-regular-atlas-block-monomial-gap
---

Let `c_0>0` be the constant from `(BMG3)`.  Apply irreducible purification
to a positive certificate.  This gives `r_i->infinity`, full coefficient
algebras `D(U_i)=M_(r_i)(C)`, and vanishing Atlas defect.  The family of real
and imaginary block coefficients has fixed finite cardinality, independent
of `i`.  By `(BMG3)`, for all sufficiently large `i` some pair has

```text
||[H_i,K_i]||_(2,r_i) >= c_0/2.                      (1)
```

Passing to one subsequence makes the two coefficient positions fixed.

Every block coefficient of a unitary block matrix is a contraction.  Hence
its real and imaginary parts are selfadjoint contractions and

```text
||[H_i,K_i]||_op <= 2.                              (2)
```

Put `C_i=[H_i,K_i]` and

```text
P_i=1_[c_0/4,infinity)(|C_i|),
alpha_i=tr_(r_i)(P_i).
```

Splitting the normalized squared Hilbert--Schmidt norm over `P_i` and its
complement, (1)--(2) give

```text
c_0^2/4
 <= ||C_i||_2^2
 <= 4 alpha_i + (c_0^2/16)(1-alpha_i).
```

Therefore

```text
alpha_i
 >= (3c_0^2/16)/(4-c_0^2/16)
 >= 3c_0^2/64.
```

This is `(MAC1)`.  Since the range of `P_i` is contained in the support of
`|C_i|`, `(MAC2)` follows immediately.  Purification, vanishing defect, and
full generation are unchanged by passage to a subsequence.
