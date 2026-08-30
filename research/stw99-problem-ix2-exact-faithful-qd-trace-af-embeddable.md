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
  - research/artifacts/stw09-matrix-coherence-rank-obstruction-2026-08-30.md
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

Trace-compatible AF embeddings also survive finite continuous gluings.  By
`stw08-continuous-block-gluings-preserve-af-embeddability`, suppose each
`tau_j` extends across a unital `A_j->E_j` with `E_j` AF.  Full-support
measures on compact metrizable `X_j` define faithful product tracial states
on `C(X_j,A_j)`.  Every positive weighted sum of their coordinate
restrictions to a common-unit C*-subalgebra of a finite direct sum extends
across the explicit unital AF embedding.  This covers traced unital finite
pullback trees and mapping tori without surjectivity of the gluing maps.  It
is a permanence theorem from existing trace-preserving embeddings, not a
coherification of an arbitrary faithful quasidiagonal trace.

There is also a strict obstruction to the most direct attempted
coherification of the given matrix trace models.  By
`stw09-full-matrix-coherence-rational-core-criterion`, if a prescribed
finite-dimensional core is represented exactly and consecutive full matrix
targets are joined by unital embeddings with norm error tending to zero,
then the limiting trace has rational weight on every minimal central
projection of the core.  For an irrational faithful trace on `C^2`, exact
matrix homomorphisms converge to the trace and give a faithful tracial
matrix-ultraproduct embedding, but no such full-matrix coherent refinement
exists.  Since `C^2` is itself AF, this refutes only the shortcut, not IX(2):
a viable proof must retain multi-summand stages and flexible compatible
traces, or obtain injectivity independently of the given trace.
