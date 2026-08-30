---
rg: 2
id: stw99-problem-xxxiii-dynamical-comparison
kind: claim
title: All free minimal amenable actions have dynamical comparison (STW Problem XXXIII)
root: true
distinct_from:
  stw99-problem-xviii-toms-winter-conjecture: that is comparison for C*-algebras where counterexamples exist (Villadsen); this is its dynamical analogue where NO counterexample is known, the status reversal STW tabulate against uniform property Gamma.
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXIII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Do all free minimal amenable actions of countable discrete groups on
compact metrisable spaces have dynamical comparison (`μ(U) < μ(V)` for
all invariant probability measures forces `U ≾ V` by equivariant open
covers)?  Kranz: no counterexample is known even for arbitrary actions
of discrete groups on compact spaces.

Known: polynomial growth (Naryshkin), and the paradoxical-tower classes
of GGKN on the non-amenable side; Kerr--Szabo: comparison + small
boundary property ⟺ almost finiteness for free actions of amenable
groups.

## Attempts

* STW's table records the striking duality with the C*-side: strict
  comparison FAILS in examples while uniform Γ was conjectured
  automatic; dynamically, comparison is conjectured automatic while
  relative Γ (= SBP) FAILS in examples (Lindenstrauss--Weiss).  The
  2026 Toms counterexample broke the C*-Γ half of this table; the
  dynamical comparison half is now the last "always holds?" cell, and
  the Toms mechanism (Schubert-calculus obstructions in the
  ALGEBRA) has no dynamical carrier: subsets of `X` have no
  characteristic classes, which is precisely why no obstruction
  candidate exists.  A refutation would need a dynamical invariant
  playing the Chern-class role for open sets — nothing in the
  literature does this; a proof needs tilings beyond subexponential
  growth.  This asymmetry (no known obstruction THEORY, not just no
  known example) is the recorded reason STW and Kerr--Szabo expect a
  positive answer.
* Downstream: `stw99-xxxiii-implies-xxxii` closes both halves of the
  crossed-product problem; with the small boundary property it also
  answers the amenable half of the classification challenge XXXIV.
