---
rg: 2
id: stw99-problem-lx-rr0-weak-cancellation
kind: claim
title: Real rank zero algebras have weak cancellation and are K1-surjective (STW Problem LX, Zhang's conjecture)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
---

**Problem LX of Schafhauser--Tikuisis--White, arXiv:2506.10902**, two
parts: (1) do real rank zero C\*-algebras have weak cancellation
(equivalently, are they separative — AGOR Question 3.2)?  (2) are they
`K_1`-surjective (Zhang's unpublished conjecture)?

Known: RR0 gives `K_0`-surjectivity (Zhang's Riesz decomposition) and
`K_1`-injectivity (Lin); AGOR: separative RR0 algebras are
`K_1`-surjective, so — since RR0 passes to matrices and stabilizations
— a positive (1) for all RR0 algebras implies (2).

## Attempts

* Route recorded (`stw99-lx-implies-xxix`): weak cancellation for
  simple RR0 algebras closes Rordam's dichotomy (STW's referee
  footnote): a mixed counterexample would have a finite projection
  `p` with `pAp ⊗ K ≅ A ⊗ K` stably finite via AGOP 7.6,
  contradiction.  So LX(1) sits strictly above XXIX in the graph, and
  any RR0 dichotomy counterexample refutes LX(1) first — the two
  problems share the finite+infinite-with-dense-cutting tension
  recorded in the RR0 cluster dossier.
* Separativity is an exchange-ring property; the known non-separative
  exchange-ring constructions (Bergman-type universal constructions
  realizing arbitrary refinement monoids) have no C*-realizations
  with RR0 — the graph-monoid realization program (Ara--Pardo school)
  hits exactly the C*-side wall that a monoid with a non-separative
  element needs an infinite projection interacting with a finite one
  in the same ideal.  The honest frontier: realize a non-separative
  refinement monoid as `V(A)` of an RR0 C*-algebra (refutes (1) and
  with it Rordam's dichotomy expectations) or prove C*-RR0 forces
  the Riesz refinement to be separative (closing (1), (2), and XXIX
  at once).
