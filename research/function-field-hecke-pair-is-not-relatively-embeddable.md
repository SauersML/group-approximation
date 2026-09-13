---
rg: 2
id: function-field-hecke-pair-is-not-relatively-embeddable
kind: claim
title: The function-field Hecke inclusion L(SL_3(F_2[t])) < L(SL_3(F_2[t,1/t])) is not relatively embeddable over the scalars
distinct_from:
  arithmetic-pair-is-not-relatively-embeddable: that is the dyadic number-field pairs SL_n(Z) < SL_n(Z[1/2]); this is the positive-characteristic one-place Laurent pair, which sits inside the Kun--Thom double at the Bowen--Chapman parameters
  kt-double-hyperlinearity-requires-function-field-hecke-re: that is the established transfer; this is the open negative statement that the transfer would turn into non-hyperlinearity of the Kun--Thom double
---

**OPEN.**  Put `Lambda=SL_3(F_2[t,1/t])=EL_3(F_2[t,1/t])` and
`C=SL_3(F_2[t])`.  The claim is that `L(C) subset L(Lambda)` is not `RE/C`.
By `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`, the following
are equivalent forms:
- the double `Lambda *_C Lambda` is non-hyperlinear;
- the binary coset wreath over `Lambda/C` is non-hyperlinear;
- the centralizer HNN group `Lambda *_C (C x Z)` is non-hyperlinear.

Here `Lambda/C` is the set of type-zero vertices of the Bruhat--Tits building
of `SL_3(F_2((t)))`.

By `kt-double-hyperlinearity-requires-function-field-hecke-re`, this claim
makes the Kun--Thom double at `(q,r,d)=(2,3,d)` non-hyperlinear for every
`d>=3`.  That includes the Bowen--Chapman Lean witness.  The same transfer
holds for every `q` and every `r>=3`.

## Attempts

- **Kun--Thom compression.**  Unavailable.  `C` is incompressible in
  `Lambda`, since its closure is a maximal compact open subgroup of
  `SL_3(F_2((t)))` (see `opposite-slice-function-field-hecke-pair-proof`).
  Theorems A, C, 4.1 and Corollary D all need a strict compressor.
- **Exact finite models.**  `C` is co-dense in every finite quotient, by the
  Laurent torus rotation (TR1).  So
  `codense-kazhdan-coset-action-forces-permutation-outliers` excludes exact
  and correctable permutation atlases.  This is a permutation statement.  It
  says nothing about unitary models of the double, which is where
  non-hyperlinearity lives.
- **Number-field template.**  The dyadic nodes
  `relative-commutant-collapse-for-sl2-pair` and
  `sl3-arithmetic-inclusion-is-not-re-over-scalars` formulate the negative
  statement as relative commutant collapse in matrix ultraproducts.  The
  formulations transfer in form, with `Q_2` replaced by `F_2((t))`.  None is
  proved in either characteristic.
- **Where it dies.**  A proof must turn Kazhdan rigidity of the co-dense base
  into rigidity of approximate unitary models that extend to `Lambda`, a flexible
  Hilbert--Schmidt stability statement for `C` at such models.  No such
  statement is known for a residually finite Kazhdan group.
