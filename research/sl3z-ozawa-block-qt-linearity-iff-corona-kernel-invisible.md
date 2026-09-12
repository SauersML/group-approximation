---
rg: 2
id: sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible
kind: claim
title: Ozawa's SL(3,Z) block algebra has only tracial quasitraces iff no quasitrace on its corona charges the trace kernel
distinct_from:
  stw01-qt-invisible-ideal-extension-principle: that transfers linearity when every bounded quasitrace on the ideal itself is zero; this is an equivalence for one host, where the condition is vanishing on the ideal of every quasitrace of the ambient corona, and failure yields a counterexample.
  stw01-full-free-group-algebra-quasitraces-are-traces: that is the universal RFD test equivalent to Problem I; this concerns one specific non-exact RFD host, and localizes any non-tracial quasitrace on it to one explicit ideal.
  sl3z-ozawa-block-corona-has-unique-trace: that computes the traces of the corona; this uses it to turn quasitrace linearity of the block algebra into vanishing on the trace kernel.
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

**ESTABLISHED (derivation `sl3z-ozawa-corona-kernel-dichotomy-proof`).** Notation as in
`sl3z-ozawa-block-corona-has-unique-trace`: `B`, `I`, `A = B/I`, the unique trace
`τ_0`, and `K = N_{τ_0} = ker(A → C*_r(SL(3,Z)))`, which is nonzero.

**Equivalence.** The following are equivalent:
1. every bounded 2-quasitrace on `B` is a trace;
2. every bounded 2-quasitrace on `A` vanishes on `K`.

A bounded 2-quasitrace on `A` that charges `K` is not a trace, so it refutes STW
Problem I.

**Sufficient conditions for (2):**
- `K` is exact; or
- every `a ∈ K_+` is infinitesimal in the Cuntz semigroup of `A`, i.e.
  `m·[(a − ε)_+] ≤ [1_A]` for all `m` and `ε`.

**General form.** Let `B ⊂ ∏ M_{n_k}` be unital, contain `⊕ M_{n_k}`, and suppose
its corona `A` has a unique trace `τ_0` with `A/N_{τ_0}` exact. Then (1) ⟺ (2) for
`B`. Neither exactness of `B` nor any comparison property is assumed.

**What it says about attacks.**
- Any non-linear quasitrace on `B` must charge `K`.
- Every unital C*-subalgebra of a corner of `∏M/⊕M` has a trace (normalized rank
  traces on the corner). So a counterexample cannot be a traceless stably finite
  corner of `A`; it must charge a non-unital part of `K`.

Proofs are in §§3–5 of the artifact.
