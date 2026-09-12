---
rg: 2
id: stw99-problem-xxiv-ash-ranks-almost-occur
kind: claim
title: All ranks almost occur in every unital simple non-elementary ASH algebra (STW Problem XXIV)
root: true
distinct_from:
  stw99-problem-xxiii-rank-problem: that asks for exact realization of all lsc affine rank functions in general stably finite algebras; this asks only for approximate realization of continuous rank functions, but in the specific ASH class without the slow-dimension-growth hypothesis under which Toms proved it.
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
---

**Problem XXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Do
all ranks almost occur in every unital simple non-elementary ASH
algebra?  Known for AH algebras (implicit in BPT Crelle Thm 5.3, sans
the sr1 hypothesis by completing the Cuntz semigroup) and for ASH
algebras of slow dimension growth (Toms, Invent. Math.).

## Attempts

* Untouched by the 2026 uniform-Γ refutation wave: Toms's Γ
  counterexample is AH, and all ranks almost occur in AH algebras, so
  it CONFIRMS an instance of this problem rather than threatening it.

* This is the exact residue of the Toms--Winter conjecture for ASH
  algebras: ASH algebras have locally finite nuclear dimension, so a
  positive answer plus strict comparison gives pureness (STW
  `prop:cu-regular` (7) ⟹ (5)), then Cuntz semigroup regularity, then
  `Z`-stability by Winter's theorem — closing Toms--Winter for all
  simple finite ASH algebras, with no stable-rank hypothesis.  STW:
  "the Toms--Winter conjecture remains open for simple finite ASH
  algebras... essentially due to Problem [XXIV]".
* The obstruction to running Toms' argument without slow dimension
  growth: his construction of elements with prescribed rank uses
  Eilenberg-swindle room in the fibre dimensions relative to base
  dimension.  In a Villadsen-type ASH system the Euler-class rigidity
  that blocks comparison (`uniformly-doubled-rordam-steps-force-proper-infiniteness`
  is the same calculus) does NOT obviously block approximate rank
  realization — rank functions only need Chern-character-level data,
  and no known characteristic-class obstruction survives the "almost"
  in almost-occurrence.  A proof would need a section-existence theorem
  below the Euler boundary; a counterexample would need a new
  obstruction stable under uniform closure.  Neither exists in the
  literature.
