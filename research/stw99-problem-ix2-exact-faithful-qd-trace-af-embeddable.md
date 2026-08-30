---
rg: 2
id: stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable
kind: claim
title: Every separable exact C*-algebra with a faithful quasidiagonal trace is AF-embeddable (STW Problem IX(2))
root: true
distinct_from:
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: that assumes quasidiagonality of the algebra; this assumes a faithful quasidiagonal trace, which implies it (Brown, Proposition 4.1.3), so this is the special case.
  stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal: that is the nuclear quasidiagonality question; this is the exact AF-embeddability question, and neither implies the other.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

**Problem IX(2) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902.**  Let `A` be a separable exact C\*-algebra with a
faithful quasidiagonal trace.  Is `A` AF-embeddable?

This is Theorem 11 of STW with the UCT removed and the trace assumed
quasidiagonal rather than merely amenable.  A faithful quasidiagonal trace
makes `A` quasidiagonal (Brown, Proposition 4.1.3), so Problem VIII implies
this (`stw99-viii-implies-ix2`).

There is an unconditional permanence result once a trace-preserving AF
embedding is available.  If a finite group preserves `tau` and
`eta:A->E` is an AF embedding with `sigma eta=tau`, then
`stw08-finite-group-crossed-products-preserve-af-embeddability` embeds
`A rtimes F` into `M_|F|(E)` and extends the canonical trace `tau E_A` by
`tr_|F| tensor sigma`.  This transports trace-coherent positive cases across
finite actions, but it does not obtain the initial embedding from a faithful
quasidiagonal trace alone.
