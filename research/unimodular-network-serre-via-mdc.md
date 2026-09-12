---
rg: 2
id: unimodular-network-serre-via-mdc
kind: route
title: Label a unimodular integral network by i.i.d. uniforms and read its weights as a self-adjoint element of the integral groupoid ring of the root-moving relation
target: serre-class-from-unimodular-integral-realizability
requires:
  - measure-theoretic-determinant-conjecture
artifacts:
  - research/artifacts/unimodular-networks-mdc-2026-09-12.md
---

Artifact Section 1.1. Let `(G,o)` be a unimodular integral network with weighted
degree at most `D`.

1. **Labels.** i.i.d. uniform labels preserve unimodularity and almost surely
   leave no nontrivial automorphism.
2. **Relation.** On labeled rooted networks with distinct labels, let `R` move
   the root. Its classes are the vertex sets, so `R` is a countable Borel
   equivalence relation. Mass transport for the labeled law is exactly
   invariance of that law under `R`.
3. **Element.** `T(x,y) = w(o,v)` lies in `ZR`, is self-adjoint, and has at
   most `D` nonzero entries per row. Since `tr(T^k) = E (A^k)_(oo)`, the
   spectral measure of `T` is the expected root measure.
4. **Conclusion.** For nonzero `Q in Z[x]`, MDC gives `det Q(T) >= 1`. By
   functional calculus this is `integral_(Q != 0) log|Q| d mu >= 0`.

This is the converse of `mdc-via-unimodular-network-serre`; the note there
explains why the cycle is intended.
