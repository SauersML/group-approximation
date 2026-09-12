---
rg: 2
id: sl3-arithmetic-double-hyperlinear-iff-relative-embeddable
kind: claim
title: The SL3 arithmetic double is hyperlinear exactly when the lattice factor inclusion is relatively embeddable over the lattice factor
artifacts:
  - research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
distinct_from:
  relatively-embeddable-pair-makes-the-hnn-group-hyperlinear: that uses Gao's unconditional enlarged amalgam and an HNN embedding for arbitrary pairs; this verifies the appendix's extra Haar-relative-unitary hypothesis and obtains an equivalence for the plain SL3 double.
  sl3-arithmetic-double-finite-representations-fold: that is an exact finite-dimensional folding theorem; this is a trace-preserving embeddability equivalence for the full tracial amalgamated free product.
  shulman-symmetric-double-has-no-stable-trace-upgrade: that concerns operator-norm MF of full C-star symmetric doubles; this is Gao's canonical-trace von Neumann algebra theorem and has no MF-to-hyperlinear gap.
---

Put

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
N=L(C) subset M=L(A),       D=A *_C A.
```

Then the following are equivalent.

1. The group `D` is hyperlinear.
2. The tracial amalgamated free product `M *_N M=L(D)` is Connes embeddable.
3. The inclusion `N subset M` is relatively embeddable with respect to `N`
   (`RE/N`) in the sense of Gao, arXiv:2012.07940, Definition 2.2.

The current proof applies the general group tensor-swap equivalence to
obtain `RE/scalars`, and then removes or adjoins the CE lattice coefficient
using `sl3-re-over-lattice-iff-re-over-scalars`. It needs no relative-Haar
element and applies to arbitrary countable subgroup pairs at the scalar
stage. The earlier source-only replay of Gao's plain-double converse has
been replaced because its printed square lacked a commutation argument.

Thus the simultaneous two-vertex-outlier problem is exactly
non-relative-embeddability of this inclusion. The ordinary binary coset
wreath and centralizer HNN group have this same hyperlinearity status.
