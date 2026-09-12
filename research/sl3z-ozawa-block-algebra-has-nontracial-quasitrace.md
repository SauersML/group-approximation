---
rg: 2
id: sl3z-ozawa-block-algebra-has-nontracial-quasitrace
kind: claim
title: Ozawa's SL(3,Z) block algebra carries a bounded quasitrace that is not a trace
distinct_from:
  sl3z-ozawa-block-algebra-quasitraces-are-traces: that is the positive statement for the same host; this is its negation, and it refutes STW Problem I.
  stw01-modular-single-pair-quasitrace-additivity: that is the positive single-pair test on the full modular group algebra; this is a counterexample statement on a Kazhdan block algebra, where the non-additivity must charge the corona trace kernel.
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

**Statement (OPEN).** Ozawa's block algebra
`B = C*(⊕_k σ_k(SL(3,Z)))` ⊂ `∏_k M_{p_k² + p_k}` carries a bounded 2-quasitrace
that is not a trace.

**Equivalent form.** By `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`,
this holds iff some bounded 2-quasitrace on the corona `A = B/⊕M` charges the trace
kernel `K = ker(A → C*_r(SL(3,Z)))`.

**Consequence.** Establishing it refutes STW Problem I,
`stw99-problem-i-quasitraces-are-traces`.

## Attempts

- **A dimension function charging `K`.** Needs some `a ∈ K_+` that is not
  infinitesimal in `W(A)`, i.e. a failure of comparison inside `A` for trace-thin
  elements. No lower semicontinuous state on `W(A)` charging `K` was found. The
  natural ones (limits of normalized block ranks) are traces and vanish on `K`.
- **Traceless unital corners (Milhøj–Rørdam Theorem 2.3).** Dead inside `A`:
  every unital C*-subalgebra of a corner of `∏M/⊕M` has a trace (normalized rank
  traces on the corner). So a counterexample cannot be a traceless stably finite
  corner; it must charge a non-unital part of `K`.
- **Kazhdan-projection non-exactness.** The certificate on main lives in
  `B ⊗_min ∏ B(H̄_j)` and gives no quasitrace.
- **Domination.** A quasitrace charging `K` is dominated by no trace (Brown–Winter
  Lemma 3 is consistent with it), so there is no leverage in either direction.
