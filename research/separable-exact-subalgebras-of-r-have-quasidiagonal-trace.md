---
rg: 2
id: separable-exact-subalgebras-of-r-have-quasidiagonal-trace
kind: claim
root: true
title: The trace of the hyperfinite II1 factor is quasidiagonal on every separable exact subalgebra
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks whether the trace of R is quasidiagonal on all of R, equivalently whether R is quasidiagonal; this asks only for its restrictions to separable exact subalgebras, and is implied both by X(2) and by the exact residual of X(1).
  amenable-traces-on-exact-cstar-algebras-are-quasidiagonal: that is the universal statement over all exact algebras and all amenable traces; this is its specialization to faithful traces with hyperfinite GNS closure realized inside R, which is the case that also sits under X(2).
artifacts:
  - research/artifacts/stw10-x1-exact-residual-2026-09-05.md
---

Let `S` be a separable exact C\*-subalgebra of the hyperfinite II1 factor
`R` and let `tau` be the restriction of the trace of `R` to `S`.  Then
`tau` is a quasidiagonal trace on `S`.

**OPEN.**  Two routes, one from each of the open questions it sits under:
`exact-r-subalgebra-traces-via-exact-x1` and
`exact-r-subalgebra-traces-via-x2`.  A counterexample would refute both STW
Problem X(2) and the exact-algebra residual of X(1) at once, so this is the
common test object for the two.

## What is unconditional

`tau` is faithful, and it is amenable: the GNS closure of `S` for `tau`
is isomorphic to the von Neumann subalgebra `W*(S)` of `R`, which is
injective as a von Neumann subalgebra of `R` with a trace-preserving
conditional expectation, and for exact `S` amenability of a trace is
injectivity of its GNS closure (Brown, Corollary 4.3.4; STW footnote 25).
Only operator-norm multiplicativity of the models is missing.

## Attempts

- Nonexact subalgebras of `R` exist (for instance inside an embedded copy
  of `prod_n M_n`), and there the amenability of the restricted trace is not
  automatic, which is why the claim is restricted to exact `S`.
- Every subalgebra of an embedded `prod_n M_n` is residually finite
  dimensional, hence has quasidiagonal traces; the content of the claim is
  the subalgebras of `R` that are exact but not norm-approximable by
  finite-dimensional algebras.
