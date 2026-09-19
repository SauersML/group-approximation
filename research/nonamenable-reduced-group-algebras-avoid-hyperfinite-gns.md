---
rg: 2
id: nonamenable-reduced-group-algebras-avoid-hyperfinite-gns
kind: claim
title: No trace on the reduced C*-algebra of a nonamenable group has injective GNS closure
distinct_from:
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that constrains which groups embed in U(R) through Kirchberg's finite-dimensional rigidity for Kazhdan groups; this constrains which C*-algebras embed in R, killing all reduced group algebras of nonamenable groups through Bekka amenability of representations, with no rigidity input.
  literal-group-mark-invisible-to-hyperfinite-representations: that kills the mark of E in hyperfinite representations of the full group; this is about traces on reduced algebras and excludes the Rosenberg mechanism (nonamenable ⟹ reduced algebra not quasidiagonal) as a source of non-quasidiagonal subalgebras of R.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `Γ` be a countable discrete group that is not amenable.  Then no tracial
state on `C*_r(Γ)` has injective (hyperfinite) GNS von Neumann closure.
Consequently `C*_r(Γ)` admits no trace-compatible embedding into the
hyperfinite II₁ factor — and since any unital embedding
`C*_r(Γ) ⊆ R` restricts the trace of `R` to a trace with injective GNS
closure, `C*_r(Γ)` does not embed into `R` at all.

**Consequence for STW Problem X(2).**  Rosenberg's theorem (the appendix to
Hadwin's paper) says `C*_r(Γ)` is not quasidiagonal for nonamenable `Γ`.
This is the easiest known mechanism producing non-quasidiagonal stably
finite algebras, and this claim shows it can never witness
`hyperfinite-factor-not-quasidiagonal`: no such algebra sits inside `R`.
Together with the peer observation that a non-quasidiagonal subalgebra of
`R` must fail exactness or the UCT (Tikuisis--White--Winter, Gabe; recorded
in `stw99-problem-x2-hyperfinite-factor-quasidiagonal`), and with the
exclusion of all known non-MF groups
(`literal-group-mark-invisible-to-hyperfinite-representations`,
`kazhdan-groups-in-hyperfinite-unitary-group-are-rf`,
`clifford-witness-has-no-hyperfinite-marked-representation`), every
recorded source of non-quasidiagonality in this lane is excluded from `R`.
