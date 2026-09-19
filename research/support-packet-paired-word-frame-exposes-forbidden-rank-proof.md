---
rg: 2
id: support-packet-paired-word-frame-exposes-forbidden-rank-proof
kind: route
title: Solve the paired commutator kernels and enumerate their symbolic isomorphisms
target: support-packet-paired-word-frame-exposes-forbidden-rank
requires: []
artifacts:
  - experiments/schur_packet_paired_commutant_frame.py
---

Let `Omega_k` be the four-by-four alternating form of the support packet at
central character `k`.  If the coefficient words in `(PWF1)` are the rows of
`C`, the paired frame has evaluated form

```text
Omega_k + C Omega_l C^t,                               (1)
```

where `l=011` on the plus side and `l=101` on the minus side.  Substitution in
`(1)` and binary elimination give `(PWF2)`.

For `k=101,l=011`, the plus form has rank two.  Its four-generator sector
algebra is therefore

```text
M_2 tensor C[(C_2)^2] = M_2^4,
```

of vector-space dimension sixteen.  Every paired word commutes with the
diagonal packet on this sector by construction, and the diagonal commutant
computed in `(CWD6)` has the same sixteen-dimensional nontrivial summand.
Containment plus equality of dimensions proves that the words span it.  For
`k=l=101`, the minus form is zero, so the corresponding sixteen words span
`C[(C_2)^4]=C^16`.  This proves the word-level realization.

For the symbolic statement, record each of the six pairwise commutators as a
vector in the six-dimensional centre of the two packet copies.  On the plus
side the three nonzero columns are

```text
(100|011), (110|110), (001|001),                      (2)
```

and on the minus side they are

```text
(100|100), (110|110), (001|001).                      (3)
```

Both lists are independent.  Their maps from `wedge^2(F_2^4)` have the same
kernel (the other three basic wedges), so a linear isomorphism of their
three-dimensional commutator centres makes the two class-two presentations
isomorphic.  Normal form gives order `2^(4+3)=128`.

Finally enumerate `GL_4(F_2)`.  Exactly 32 matrices preserve the common
exterior-square relation kernel.  Pulling the evaluated minus forms back by
these matrices yields eight distinct permutations of the eight source
central characters.  Direct substitution in `(1)` shows that all 32 send
the plus form at `101` to the minus form at `011`; no other target has the
same evaluated form.  This proves `(PWF3)`.  The accompanying standard-library
experiment exhausts all 65,536 binary four-by-four matrices and checks every
displayed rank, kernel and transport statement exactly.
