---
rg: 2
id: fixed-semisimple-trace-chart-multiplicity-proof
kind: route
title: Compute every reflected rank from irreducible multiplicities
target: semisimple-trace-charts-cannot-authenticate-proper-fullness
requires: []
artifacts:
  - research/artifacts/fanizza-finite-chart-trace-reflection-criterion-2026-08-21.md
---

Decompose a finite-dimensional C-star algebra as
`A=direct_sum_j M_(d_j)(C)`.  Every finite-dimensional representation is a
direct sum of the defining irreducibles with multiplicities `m_j`.  Taking
the ordinary normalized matrix trace gives `(FTR3)`.

Choosing a representation supported on one simple summand proves that this
ratio is independent of all multiplicities exactly when each sector ratio
is the same.  If `g<=e` and their traces agree in every representation, the
positive projection `e-g` has rank zero in each simple summand.  Hence
`e-g=0`, proving the claimed fullness dichotomy.

For a fixed faithful profile `m_j=L a_j`, a nonzero chart projection has
some sector rank at least one, so its normalized trace is at least
`min_j a_j/(sum_i a_i d_i)`.  This proves the dimension-free quantization
gap and isolates algebra-factor localization as the remaining hypothesis.
