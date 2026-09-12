---
rg: 2
id: hilbert-hotel-cstar-total-invisibility
kind: claim
title: The Hilbert-hotel reduced group C-star algebra has no nonzero MF image
distinct_from:
  hilbert-hotel-model-full-mf-radical: that is the group theorem; this computes all MF-target homomorphisms and all MF quotients of both canonical group C-star completions.
  exact-stably-finite-non-mf-reduced-group-algebra: that proves existence of a stably finite non-MF reduced algebra; this says every nonzero quotient of the concrete Hilbert-hotel reduced algebra remains non-MF.
artifacts:
  - research/full-mf-radical-cstar-reflection.md
  - research/hilbert-hotel-cstar-total-invisibility-proof.md
---

Let

```text
H = EL_16(L_(F_2)(1,2)).
```

Then every star homomorphism from `C*_r(H)` to an MF C-star algebra is zero.
In particular every nonzero quotient of `C*_r(H)` is non-MF, although
`C*_r(H)` itself is stably finite through its faithful canonical trace.

Every star homomorphism from `C*_max(H)` to an MF C-star algebra factors
through augmentation.  Hence the maximal MF-visible quotient of
`C*_max(H)` is exactly `C`, while the reduced algebra has zero MF-visible
quotient.

Thus the two canonical completions have opposite scalar behavior:

```text
C*_max(H)  --MF reflection-->  C,
C*_r(H)    --MF reflection-->  0.
```
