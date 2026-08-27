---
rg: 2
id: mf-camouflage-faithful-functor-proof
kind: route
title: Apply the amalgam universal property and the regular-star normal form
target: mf-camouflage-is-a-faithful-split-extension-functor
requires:
  - camouflage-kernel-is-a-regular-star-amalgam
  - mf-semantic-closure-transplantation
---

For `f:Q->R`, the identity map on `B` and the map

```text
f x id_D:Q x D -> R x D
```

agree on the common subgroup `D`.  The amalgam universal property therefore
defines `C_d(f)`.  Uniqueness gives preservation of identities and
composition, while restriction to the canonical copy of `Q` proves that the
functor is faithful.  The definitions immediately give naturality of `pi`
and `s` and the split identity `(FSF1)`.

If `f` is onto, `C_d(f)` contains both generating vertex groups of the
target and is onto.  If `f` is injective, use `(RSA1)`: on the kernel it is
the canonical inclusion

```text
*_(D,q in Q) B_q -> *_(D,r in R) B_r
```

associated to the injection of indexing sets.  Generalized amalgam normal
form makes this map injective.  The induced map on the split quotient is
`f`, so the semidirect-product normal form in `(RSA2)` proves that `C_d(f)`
is injective.

The three properties of `pi_Q` are respectively `(RSA2)--(RSA3)`, the
universal MF-target factorization theorem, and MF semantic-closure
transplantation.
