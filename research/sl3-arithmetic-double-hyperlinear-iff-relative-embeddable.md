---
rg: 2
id: sl3-arithmetic-double-hyperlinear-iff-relative-embeddable
kind: claim
title: The SL3 arithmetic double is hyperlinear exactly when the lattice factor inclusion is relatively embeddable over the lattice factor
artifacts:
  - research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md
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

This is Gao's Appendix Theorem 7.1, including rather than suppressing its two
extra hypotheses for the plain double:

```text
N_1=N must be a finite factor;
there is u in U(M) with E_N(u^n)=0 for every n!=0.            (GRE1)
```

Both hold for the arithmetic inclusion.  Therefore the simultaneous
two-vertex-outlier problem is exactly non-relative-embeddability of one
explicit inclusion; no enlargement by an `L(Z)` tensor factor is needed in
rank three.
