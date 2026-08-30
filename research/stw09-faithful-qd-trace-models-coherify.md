---
rg: 2
id: stw09-faithful-qd-trace-models-coherify
kind: claim
title: Faithful quasidiagonal trace models admit trace-coherent refinement
distinct_from:
  stw09-trace-preserving-af-embedding-iff-trace-coherent-models: that established criterion identifies trace-coherent systems with trace-preserving AF embeddings; this is the open existence of such a system from exactness and a faithful quasidiagonal trace.
  stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable: that only asks for an AF embedding, whereas this asks for the stronger trace-preserving embedding encoded by compatible model traces.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
  - research/artifacts/stw09-matrix-coherence-rank-obstruction-2026-08-30.md
---

If `A` is separable and exact and `tau` is a faithful quasidiagonal trace on
`A`, then the independent matricial approximations defining quasidiagonality
of `tau` can be refined to a trace-coherent system as in
`stw09-trace-preserving-af-embedding-iff-trace-coherent-models`.

This stronger trace-preserving form of Problem IX(2) is open.

## Attempts

Faithfulness shows that the homomorphism defined by the independent trace
models in a matrix quotient is injective, but it does not connect different
matrix coordinates.  Amplifying and block-summing coordinates preserves old
operator-norm multiplicative defects and does not create compatible traces on
an injective finite-dimensional system.  The missing theorem is a stable
uniqueness/amalgamation statement which simultaneously matches point-norm
finite models and their trace weights.  The UCT case supplies such global
compatibility through the established trace-preserving AF-embedding theorem;
no UCT-free replacement is assumed here.

One seemingly stronger normalization is actually false.  The independent
models cannot in general be restricted to full matrix stages with their
normalized traces and then connected by unital embeddings.  The theorem
`stw09-full-matrix-coherence-rational-core-criterion` shows that norm
coherence freezes the normalized ranks of exact core projections and hence
forces rational central trace weights.  An irrational faithful trace on
`C^2` violates this while `C^2` is already AF.  Thus the finite-dimensional
algebras and compatible traces in the formulation above must retain their
multi-summand flexibility.
