---
rg: 2
id: schur-flip-rank-is-residual-atomic-granularity
kind: claim
title: Schur flip rank tests the atomic trace granularity of the residual multiplicity factor
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-flip-cells-expose-residual-matrix-tape: that factors the old cells and states the divisor imposed by additional cocycle rank; this identifies the divisor with the smallest trace of a nonzero residual projection and contrasts matrices with diffuse tracial factors.
  schur-residual-commutant-is-a-dimension-oracle-tape: that detects `L` through an additive polynomial identity; this gives a bounded group-native challenge which need not compute `L`, but must adaptively split past its atomic scale.
---

On the residual factor `M_L(C)` from `(RMT1)`, `r` independent new Schur
flip cells are equivalent to a unital copy of the Pauli algebra

```text
M_(2^r)(C) subset M_L(C).                                        (RAG1)
```

The minimal projections of this copy have normalized residual trace `2^(-r)`
and matrix rank `L/2^r`.  Consequently

```text
(RAG1) exists  iff  2^r divides L,                               (RAG2)
```

and the supercritical condition `r>log_2L` asks for a nonzero projection
strictly below the atomic trace floor `1/L`.

By contrast, every diffuse finite factor contains projections of every trace
in `[0,1]`, hence unital copies of `M_(2^r)(C)` for every finite `r`.  A nested
dyadic tower supplies the exact infinite-tracial completeness model for an
unbounded sequence of flip cells.

Thus the group-native residual dimension oracle is not required to evaluate
or invert the Amitsur--Levitzki polynomials.  It may instead keep splitting a
full-support packet cell into two Pauli children until it requests a nonzero
piece below the current matrix atom.  The unresolved quantitative condition
is the same: the stopping depth must be chosen from the current microstate,
and the aggregate splitting and return error must stay bounded independently
of that depth.  A fixed external splitting depth remains dilutable.

