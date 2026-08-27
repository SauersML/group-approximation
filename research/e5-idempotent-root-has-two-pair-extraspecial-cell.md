---
rg: 2
id: e5-idempotent-root-has-two-pair-extraspecial-cell
kind: claim
title: Every E5 idempotent root is the center of a two-pair extraspecial cell
distinct_from:
  toeplitz-defect-roots-form-independent-heisenberg-cells: That constructs one Heisenberg pair for each of many orthogonal idempotents; this constructs two mutually transverse pairs with one common central root for a single idempotent.
  extraspecial-common-gauge-fourier-controller: That uses a separately adjoined Pauli packet to control a payload representation; this cell consists entirely of canonical Steinberg roots of the same coefficient idempotent.
---

**ESTABLISHED.**  Let `R` be a ring of characteristic `p`, let `a in R` be
an idempotent, and work in `St_5(R)` or `E_5(R)`.  Put

```text
X_1=x_12(a),       Y_1=x_23(a),
X_2=x_14(a),       Y_2=x_43(a),       Z=x_13(a).       (ETC1)
```

The Steinberg commutator relations and `a^2=a` give

```text
[X_1,Y_1]=Z,       [X_2,Y_2]=Z,                       (ETC2)
```

while every cross commutator between the first and second pair is trivial.
All five generators have order dividing `p`, and `Z` is central in the
generated subgroup.  Thus `(ETC1)` is a quotient of the order-`p^5`
two-pair finite Heisenberg/extraspecial packet

```text
H_(p,2)=<X_i,Y_i,Z | [X_i,Y_i]=Z,
 all other basic commutators=1, X_i^p=Y_i^p=Z^p=1>.
                                                               (ETC3)
```

In every unitary representation, restrict to a spectral sector on which
`Z` has a fixed nontrivial `p`th-root eigenvalue.  Finite
Stone--von Neumann theory identifies that sector as

```text
l2(F_p^2) tensor M,                                   (ETC4)
```

with the packet acting by its unique `p^2`-dimensional Schrödinger
representation on the first factor.  The commuting pair `(X_1,X_2)` has
all `p^2` joint characters there with equal multiplicity.  Hence, if
`R_(r,s)` is any of its joint Fourier projections and `E_Z` is the central
sector projection,

```text
tr(R_(r,s) E_Z)=p^(-2) tr(E_Z).                        (ETC5)
```

More generally, if `P<=E_Z` commutes with the whole packet, then

```text
tr(P R_(r,s))=p^(-2) tr(P).                            (ETC6)
```

For fixed `p`, `(ETC5)--(ETC6)` have a dimension-independent normalized-HS
version after finite-packet exactification and averaging an approximately
central `P` into the packet commutant.

This supplies the transverse uniformity missing from a bare additive
three-line table.  It does not show that a BCS projection has positive mass
in the nontrivial spectral support of `Z=x_13(a)`.  That transfer is the
prescribed-carrier root-kernel/Morita decoder and remains separate.

