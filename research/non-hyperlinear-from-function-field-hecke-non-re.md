---
rg: 2
id: non-hyperlinear-from-function-field-hecke-non-re
kind: route
title: A non-relatively-embeddable function-field Hecke pair makes its double non-hyperlinear
target: non-hyperlinear-group
requires:
  - function-field-hecke-pair-is-not-relatively-embeddable
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
---

Apply items 4 and 6 of
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` to
`C=SL_3(F_2[t]) <= A=SL_3(F_2[t,1/t])`.  If `L(C) subset L(A)` is not `RE/C`,
then the double `A *_C A` is non-hyperlinear.  It is a countable group, so it
is a non-hyperlinear group.  By
`kt-double-hyperlinearity-requires-function-field-hecke-re`, the Kun--Thom
double at `(2,3,3)` contains it and is non-hyperlinear too.  That conclusion is
not needed for this route.
