---
rg: 2
id: kt-q2-double-hyperlinear-iff-relative-embeddable
kind: claim
title: Hyperlinearity of the binary Kun--Thom double is exactly relative embeddability of its von Neumann inclusion over the scalars
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: that asks for an operator-norm lift of the canonical trace; this is the exact Hilbert--Schmidt/Connes-embeddability criterion and is formally weaker, with no converse asserted.
  kt-double-reduced-cstar-is-mf: that asks for operator-norm approximation of all reduced C-star norms; this asks only for a tracial embedding of the group von Neumann algebra.
  kt-double-mixed-word-trace-selection: that gives an elementary group-microstate formulation of the same hyperlinearity question; this identifies the equivalent operator-algebraic property of the one vertex inclusion.
artifacts:
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

For the binary Kun--Thom pair, put

```text
N=L(Gamma) subset M=L(G),             D=G *_Gamma G.
```

Then the following are equivalent.

1. `D` is hyperlinear.
2. `M *_N M=L(D)` embeds trace preservingly into `R^omega`.
3. The inclusion `N subset M` is relatively embeddable over the scalars
   (`RE/C`) in the sense of Gao, arXiv:2012.07940v3, Definition 2.2.

Thus the fixed Kun--Thom candidate is not merely an unspecified instance of
the open nonamenable-amalgamation problem: its hyperlinearity is exactly one
concrete relative-embeddability question.

DERIVATION
kt-q2-double-gao-relative-embedding-proof
