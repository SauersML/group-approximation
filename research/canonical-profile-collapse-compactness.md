---
rg: 2
id: canonical-profile-collapse-compactness
kind: claim
title: Qualitative collapse on canonical microstates has a non-effective finite-window form
distinct_from:
  hyperlinear-radical-presentation-compactness: that quantifies over every matrix-ultraproduct homomorphism and uses only relator windows; this restricts to canonical-delta trace homomorphisms and permits finite canonical moment windows.
  trace-conditioned-reverse-kleene-collapse: that requires the compiler to output computable side-test tolerances; the finite windows and tolerances here exist semantically and need not be computable.
  fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity: that consumes explicit depth-dependent estimates for one fixed finitely presented group; this is the compactness equivalence for a finite or recursively enumerable presentation and an arbitrary finite group-algebra mark.
---

Let `Gamma=<S|r_1,r_2,...>` have finite `S` and a finite or recursively
enumerable relator list, and let `p in Q[F(S)]` have finite support. The
following are equivalent.

1. Every sequence of finite-dimensional tuples `U_n` satisfying every fixed
   relator asymptotically and converging on every word trace to the canonical
   character of `Gamma` satisfies

   ```text
   ||p(U_n)||_2 -> 0.                                      (CPC1)
   ```

2. For every `epsilon>0` there are a finite relator window `R_0`, a finite
   word window `F`, and numbers `delta,eta>0` such that every finite-dimensional
   tuple satisfying

   ```text
   max_(r in R_0)||r(U)-I||_2<delta,
   max_(v in F)|tr(v(U))-tau_Gamma(v)|<eta
   ```

   also satisfies `||p(U)||_2<epsilon`.

The windows and tolerances need not be computable from the presentation. The
claim remains meaningful when `Gamma` is not hyperlinear: then canonical
microstate sequences do not exist, and compactness produces a finite local
certificate of that failure or of marked collapse.
