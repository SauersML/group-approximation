---
rg: 2
id: smith-serre-measures-are-conjugate-limits
kind: claim
title: On a compact real set of capacity above one, Smith's log inequalities characterize weak limits of Galois orbits of totally real algebraic integers
distinct_from:
  integral-spectral-limits-satisfy-serre-inequalities: that proves the easy direction for limits of integer spectra, with zero sets excluded from the integral; this is the literature converse for sequences of distinct orbits, where the integral runs over zeros too and so rules out atoms at algebraic numbers
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes the purely atomic Serre-class measures; this characterizes limits of distinct orbits, which carry no atoms at algebraic numbers
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

**ESTABLISHED (literature import)** by
`smith-serre-measures-conjugate-limits-citation`.

A. Smith, *Algebraic integers with conjugates in a prescribed distribution*,
arXiv:2111.12660v2 (16 Mar 2024), page 4, read from the PDF:

> **Theorem 1.5.** Take `Σ` to be a compact subset of `R` with at most countably
> many components. We assume that `Σ` has capacity strictly larger than 1 (see
> Definition 2.1). Then, for any Borel probability measure `μ` with support
> contained in `Σ`, the following two conditions are equivalent:
> (1) For every nonzero integer polynomial `Q`, `∫_Σ log|Q(x)| dμ(x) ≥ 0`.
> (2) There is an infinite sequence of distinct irreducible monic integer
> polynomials `R_1, R_2, ...` such that the support of `μ_(R_k)` is contained in
> `Σ` for every `k` and such that `μ_(R_1), μ_(R_2), ...` has weak* limit `μ`.

`μ_R` is the uniform measure on the roots of `R` (Definition 1.4). Capacity is
logarithmic capacity (Definition 2.1). The theorem gives
`λ_SSS < 1.89831`, refuting the Schur--Siegel--Smyth trace problem
(Theorem 1.1).

**How it differs from the repository's Serre class.** Condition (1) integrates
over all of `Σ`, zeros of `Q` included. So a measure obeying it has no atom at an
algebraic number, and by `serre-class-atoms-obey-degree-bound` none at all. The
Serre class of `determinant-conjecture-iff-serre-class-spectra` excludes zero
sets and does admit atoms. The bridge between the two is
`integer-root-limits-are-galois-balanced-serre-measures`.

Trust surface: arXiv version 2, whose acknowledgments thank anonymous referees.
Journal publication was not checked.
