---
rg: 2
id: popa-projection-formulations-of-x2
kind: claim
title: Quasidiagonality of the hyperfinite factor is equivalent to norm Folner projections and to the local-AFD criterion
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that is the open question whether R is quasidiagonal; this is an unconditional equivalence theorem between three formulations of it, imported from the literature.
  stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses: that reduces X(2) across subalgebras of R; this reformulates X(2) itself at the level of finite-rank projections on L2(R) and finite-dimensional subalgebras of R, with no subalgebra quantifier.
artifacts:
  - research/artifacts/x2-popa-formulations-ingestion-2026-08-30.md
---

Let `R` be the hyperfinite II₁ factor in its trace representation on
`L²(R)`.  The following are equivalent:

1. `R` is quasidiagonal as a C\*-algebra (Problem X(2),
   `stw99-problem-x2-hyperfinite-factor-quasidiagonal`);
2. **norm Folner projections:** for every finite `F ⊂ U(R)` and
   `ε > 0` there is a nonzero finite-rank projection `p₀` on `L²(R)`
   with `‖u p₀ u* − p₀‖ < ε` for all `u ∈ F`;
3. **local AFD:** for every finite `Y ⊂ R` and `ε > 0` there is a
   nonzero finite-dimensional \*-subalgebra `B ⊂ R` with support
   projection `s` such that `‖[y, s]‖ < ε` and
   `‖s y s − E_B(s y s)‖ < ε` for all `y ∈ Y`.

For (1) ⟺ (2): `R ∩ K(L²(R)) = 0`, so the trace representation is
essential and Voiculescu's theorem makes abstract quasidiagonality of
`R` equivalent to quasidiagonality of this one representation, which
is exactly (2) on unitaries (unitaries span).

What hyperfiniteness gives unconditionally is only the normalized
Hilbert--Schmidt weakening of (2) — Connes' Folner condition
`‖u P u* − P‖_{2,Tr} < δ ‖P‖_{2,Tr}` — and the gap between the two is
the entire content of X(2): see the `## Attempts` of
`norm-folner-projections-for-hyperfinite-factor` for the checked
rank-`n` projection pair showing the upgrade admits no dimension-free
conversion.
