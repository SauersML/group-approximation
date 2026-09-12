---
rg: 2
id: sl3-arithmetic-double-gao-equivalence-proof
kind: route
title: Tensor the binary swap coefficient and remove the CE lattice coefficient
target: sl3-arithmetic-double-hyperlinear-iff-relative-embeddable
requires:
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - sl3-re-over-lattice-iff-re-over-scalars
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
  - research/artifacts/centralizer-hnn-relative-embedding-audit-2026-09-07.md
---

Put `C=SL_3(Z)`, `A=SL_3(Z[1/2])`, and `N=L(C)`. The first prerequisite
applies to every countable subgroup pair and gives

```text
A *_C A hyperlinear iff L(C)<=L(A) is RE/scalars.
```

The second prerequisite identifies `RE/scalars` with `RE/N`, because the
lattice group is residually finite and `N` is Connes embeddable. The
canonical identity `L(A *_C A)=L(A)*_(L(C))L(A)` gives the factor version.
These implications prove all three assertions of the target.

This replaces the earlier source-only use of Gao's plain-double converse.
Its printed square did not justify commutation of the dyadic diagonal
with `N`; the attached audit gives an explicit elementary-matrix witness
to the missing inclusion. The tensor proof is independent of that step
and requires no relative-Haar element in `A`.
