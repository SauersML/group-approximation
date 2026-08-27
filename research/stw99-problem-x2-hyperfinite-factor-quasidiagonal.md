---
rg: 2
id: stw99-problem-x2-hyperfinite-factor-quasidiagonal
kind: claim
title: The hyperfinite II1 factor is quasidiagonal (STW Problem X(2))
root: true
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: that quantifies over all amenable traces on all C*-algebras; this is the single instance of the trace of R, which STW expect to be the heart of the non-exact case.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem X(2) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  Is the hyperfinite II₁ factor `R` quasidiagonal
(as a C\*-algebra)?

Since `R` has a unique trace and that trace is faithful, this is equivalent to
asking whether `τ_R` is a quasidiagonal trace (Brown's Proposition 4.1.3
argument: a faithful quasidiagonal trace makes the algebra quasidiagonal by
Voiculescu's characterization).  `τ_R` is amenable, by Connes' Følner
condition for `R` (Brown, Theorem 3.1.7(3)), so a positive answer to
Problem X(1) gives a positive answer here (`stw99-x1-implies-x2`).

STW: "It seems likely to us that for not necessarily exact C*-algebras, the
heart of the matter is whether the trace on the hyperfinite II₁ factor is
quasidiagonal."  Not to be confused with `stw99-problem-xciv-hyperfinite-factor-separably-z-stable`.
