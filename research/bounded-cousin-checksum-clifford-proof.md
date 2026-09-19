---
rg: 2
id: bounded-cousin-checksum-clifford-proof
kind: route
title: Evaluate balanced commutators by parity and holonomies by finite factor permutations
target: bounded-cousin-checksums-have-finite-clifford-models
requires:
  - first-cousin-cross-arm-breaks-three-state-reuse
  - bounded-tagged-mark-seam-complex-has-finite-row-range
  - full-depth-one-leavitt-menu-has-finite-clifford-model
---

For `(BCH1)`, substitute the intended table values

```text
([X_alpha,Z_alpha],[X_beta,Z_beta],
 [X_alpha,Z_beta],[X_beta,Z_alpha])=(J,J,1,1).
```

Since `J` is a central involution, their signed product is one.  Under the
collision substitution all four entries are `J`, whose product is again
one.  The same calculation proves the even-parity assertion for any central
checksum.

For the finite holonomy model, let `V` be the finite set of cousin
occurrences named by the proposed bounded word and put

```text
H_V=C^3 tensor (C^2)^(tensor V) tensor l^2(Omega),     (1)
```

where `Omega` is the finite set of root-position and address roles appearing
in the word.  Use the three character signs on `C^3`.  For each `v in V`,
put its same-site pair on the Pauli factor `v`, controlled by the negative
projection of the required character sign.  Distinct factors give every
requested crossed-zero commutator exactly.

Each address holonomy in the bounded menu specifies a permutation of the
finite occurrence/role set, possibly followed by a binary symplectic
relabeling of the Pauli exponents.  Implement the first part on
`l^2(Omega)` and by tensor-factor permutations, and the second inside the
finite Clifford group on `(C^2)^(tensor V)`.  Define every transported
occurrence by literal conjugation.  All conjugacy squares and compressed
holonomy loops then commute exactly.

The generated monomial/Clifford group is finite and contains the nonidentity
character sign `J`.  Its left regular representation keeps `J` nontrivial
and satisfies every relation which is a consequence of the bounded menu.
The pairwise mark-seam formulation is also covered abstractly by
`bounded-tagged-mark-seam-complex-has-finite-row-range`.

If a checksum has odd collision parity, replacing one crossed value `1` by
`J` changes the checksum by `J`; hence it detects that collision.  But this
is precisely an asymmetric cross-arm constraint.  The fresh-factor model
above satisfies any fixed finite collection, and the preceding cousin claim
records why the unbounded canonical collection cannot have uniform
fixed-prototype area.
