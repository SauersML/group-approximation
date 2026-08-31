---
rg: 2
id: hyperfinite-ultrapower-trace-not-quasidiagonal
kind: claim
title: The trace of the hyperfinite ultrapower is not quasidiagonal
distinct_from:
  matrix-tracial-ultraproduct-trace-not-quasidiagonal: that is the matrix-ultraproduct statement this one is deduced from through the unital trace-preserving inclusion of the matrix ultraproduct into R^omega; the ultrapower statement is the form Popa's R^omega suggestion runs into.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that is the question for R; this settles the analogous question for R^omega negatively and unconditionally, and the two are independent because quasidiagonality of a trace restricts down but never ascends, while non-quasidiagonality does the opposite.
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

For every free ultrafilter `ω`, the ultralimit trace `τ_{R^ω}` on the
tracial ultrapower `R^ω = ℓ^∞(R)/{(x_n) : ‖x_n‖₂ → 0 along ω}` is not
a quasidiagonal trace.

So of the three algebras `R ⊂ Q ⊂ R^ω` (with `Q` a tracial matrix
ultraproduct, all inclusions unital and trace-preserving), the outer
two now have unconditionally non-quasidiagonal traces, and Problem
X(2) is exactly the innermost case.  A positive X(2) would mean
quasidiagonality of traces fails ultrapower permanence in the
strongest possible way; a negative X(2) would extend the non-QD zone
down to `R` itself.  Neither direction is forced: restriction
preserves quasidiagonality, not its negation.
