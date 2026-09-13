---
rg: 2
id: opposite-transvection-slice-is-not-relatively-embeddable
kind: claim
title: For some parameters the opposite-transvection Kun--Thom slice inclusion is not relatively embeddable over the scalars
distinct_from:
  opposite-transvection-slice-is-relatively-embeddable: that is the positive polarity for all parameters; this is its negation
  function-field-hecke-pair-is-not-relatively-embeddable: that is the one-place Hecke sub-pair at (2,3); this is the slice that contains it, which is formally weaker to refute
---

**OPEN.**  There are a prime power `q` and `r,d>=3` such that
`L(Gamma) subset L(P)` is not `RE/C` for the opposite-transvection slice
`P`.  By (OTG3), `P *_Gamma P` is then non-hyperlinear.  It is a subgroup
of the Kun--Thom double, so the Kun--Thom double at those parameters is
non-hyperlinear too.

## Attempts

A non-`RE/C` proof for the function-field Hecke pair would prove this claim
(route below).  No argument that uses the free compressor monoid is known.
Kun--Thom compression acts on the slice, but its normalization step needs an
ambient Kazhdan model.  `P` is not Kazhdan.
