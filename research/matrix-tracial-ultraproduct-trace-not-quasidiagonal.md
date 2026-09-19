---
rg: 2
id: matrix-tracial-ultraproduct-trace-not-quasidiagonal
kind: claim
title: The ultralimit trace on a tracial matrix ultraproduct is never quasidiagonal
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks about the trace of R itself, which embeds trace-preservingly into the tracial matrix ultraproduct; quasidiagonality restricts DOWN subalgebras, so this unconditional non-quasidiagonality upstairs decides nothing about R — it fences off proof strategies instead.
  stw99-problem-x1-fails-on-full-group-algebras: that produces one amenable non-quasidiagonal canonical trace on a full group algebra; this pushes it forward through the amenability homomorphism to make the universal matrix-ultraproduct trace itself non-quasidiagonal, for every size sequence and every free ultrafilter.
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

Let `(k_n)` be any sequence with `k_n → ∞`, `ω` a free ultrafilter, and

```text
Q = ∏_ω M_{k_n} / J_HS,   J_HS = {(x_n) : lim_ω ‖x_n‖₂ = 0},
```

the tracial (2-norm) matrix ultraproduct — a II₁ factor — with ultralimit
trace `τ_ω([x_n]) = lim_ω tr_{k_n}(x_n)`.  Then `τ_ω` is **not** a
quasidiagonal trace on `Q`.

Two consequences:

1. **The trace of `R^ω` is not quasidiagonal** — see
   `hyperfinite-ultrapower-trace-not-quasidiagonal`.
2. **Fence on X(2) strategies.**  Since quasidiagonality of a trace
   restricts to unital subalgebras but never ascends, no positive proof
   of `stw99-problem-x2-hyperfinite-factor-quasidiagonal` can proceed by
   establishing quasidiagonality of an ambient ultraproduct or
   ultrapower trace and restricting to `R`: every such ambient trace is
   now unconditionally non-quasidiagonal.  In particular Popa's
   suggestion to run the Gaussian-functor conversion "inside `R^ω`"
   (`popa-projection-formulations-of-x2`) must be read as constructing
   `R`-specific norm-Folner projections while computing in `R^ω`, not as
   proving anything quasidiagonal upstairs.  Likewise the amenability of
   `τ_R` — the trace-preserving embedding `R ⊂ Q` with u.c.p. lift — is
   provably useless as stated: the codomain trace is non-QD, so only
   information about how `R` sits inside `Q` can help.
