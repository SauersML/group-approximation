---
rg: 2
id: stw93-residual-tracefree-iff-unique-trace
kind: claim
title: Residual XCIII bounded-trace-freeness is exactly uniqueness of the ordinary central trace
distinct_from:
  stw93-hereditary-exhaustion-reduces-to-traces: that theorem needs hereditary quasitrace-linearity to identify ordinary traces with all quasitraces; this equivalence is unconditional but concerns ordinary bounded traces only.
  stw93-residual-trace-kernel-is-quasitrace-null: that open claim asks every quasitrace to annihilate the residual ideal; the present theorem exactly characterizes only the bounded-trace obstruction and does not linearize arbitrary quasitraces.
  stw93-singular-trace-kernel-witness-for-any-negative-answer: that theorem extracts a positive element detected by an arbitrary quasitrace; here a bounded residual trace is extended canonically to an ordinary ambient trace.
artifacts:
  - research/artifacts/stw93-residual-bounded-trace-audit-2026-08-30.md
  - research/artifacts/stw93-central-commutator-lifting-audit-2026-08-30.md
---

Put

```text
E=D/K_Z^sat,                  R=I/K_Z^sat triangleleft E.
```

The following are equivalent, without any sigma-unitality, exactness, or
hereditary-exhaustion hypothesis:

```text
(a) R carries no nonzero bounded trace;
(b) E has a unique normalized trace;
(c) D has a unique normalized trace.
```

Therefore the ordinary-tracial half of the residual XCIII obstruction is
exactly uniqueness of the trace on the norm central sequence algebra.  A
nonzero bounded trace on `R` is not merely a local warning: it canonically
extends and normalizes to a trace on `D` different from the limit trace, and
hence gives a negative answer to XCIII.

This criterion does not assert that `R` is bounded-trace-free.  In fact the
currently established saturated Jiang--Su-slice structure alone cannot
force that conclusion; see
`stw93-saturated-slice-data-allow-residual-trace`.

The actual central-sequence realization supplies one further unconditional
fact.  By `stw93-central-commutator-lifting-is-trace-hinge`, every
self-adjoint element of `I` is already a norm limit of self-commutators in
the full ultrapower `A_omega`.  The criterion above holds exactly when
those decompositions can instead be made with norm-central factors, i.e.
inside `D`.  Coordinatewise Powers--Dixmier averaging produces the ambient
factors but does not make their varying averaging unitaries central.
