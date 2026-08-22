---
rg: 2
id: elementary-bcs-canonical-unitary-compiler-fence
kind: claim
title: Canonical elementary matrices over a BCS algebra do not define a group C-star quotient, and abstract repair is the missing character theorem
requires: []
distinct_from:
  char-p-weyl-blocks-local-commutator-decoder: that studies abstract unitary root tables and their failure to recover coefficient traces; this rules out the canonical coefficient-matrix representation before any approximate decoder is considered.
  finite-normal-signed-bcs-quotient-collapses-to-twisted-factor: that analyzes trace promotion after a signed quotient exists; this shows why the elementary-ring construction does not supply that quotient.
---

Let `R` be a star subring of a C-star algebra `B`.  For `i!=j`, the canonical
elementary matrix `I+a e_ij` in `GL_n(B)` is unitary only when `a=0`, because

```text
(I+a e_ij)^*(I+a e_ij)
 = I+a e_ij+a^* e_ji+a^*a e_jj,
```

whose `(i,j)` entry is `a`.  Hence the canonical representation of
`EL_n(R)` or its Steinberg cover in matrices over `B` is not a unitary
representation and does not integrate to a star homomorphism

```text
C*(EL_n(R)) -> M_n(B).
```

Polar decomposition and unitary dilation are not multiplicative.  Algebraic
hyperbolic unitary Steinberg groups preserve an indefinite form, not the
positive C-star inner product, so they do not repair this canonical map.

One may instead posit an unrelated abstract unitary representation of an
elementary group which generates the non-CE GNS factor.  But the available
factorial-character theorems cover arithmetic special linear groups
(Peterson--Thom) or elementary groups over commutative Noetherian rings
(Lavi--Levit), not a noncommutative BCS star ring.  For an arithmetic group,
operator-algebraic superrigidity says that such a generating infinite factor
representation is already the regular factor; if its trace is non-CE, the
group is already nonhyperlinear.  Thus the abstract repair requires exactly
the missing character/groupification theorem and is not supplied by the
elementary coefficient construction.

See `research/artifacts/finite-type-corner-clifford-collapse-2026-08-21.md`.

