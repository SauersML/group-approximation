---
rg: 2
id: stw99-problem-xviii-toms-winter-conjecture
kind: claim
title: Strict comparison forces Jiang--Su stability (STW Problem XVIII, Toms--Winter)
root: true
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that asks whether every stably finite algebra in the class has uniform property Gamma; uniform Gamma together with strict comparison is a sufficient route to this problem, but the two assertions are not equivalent.
  stw99-problem-xxv-unique-trace-sr1-z-stable: that assumes unique trace and stable rank one instead of strict comparison.
  stw99-problem-xxvi-cu-regularity-z-stability: that assumes Jiang--Su absorption at the level of the Cuntz semigroup, a stronger regularity input than strict comparison alone.
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

**Problem XVIII of Schafhauser--Tikuisis--White, _Nuclear C*-algebras:
99 problems_, arXiv:2506.10902.**  Let `A` be a simple, separable, nuclear,
non-elementary C*-algebra with strict comparison.  Must

```text
A ~= A tensor Z?
```

This is the remaining strict-comparison-to-Jiang--Su-stability direction of
the Toms--Winter conjecture.  It remains open in this generality.

## Attempts and established boundaries

- The converse implications are known: Jiang--Su stability gives finite
  nuclear dimension in the simple nuclear setting, and Jiang--Su stability
  gives strict comparison.
- In the unital stably finite case, strict comparison together with uniform
  property Gamma implies Jiang--Su stability.  Toms's 2026 counterexample to
  universal uniform Gamma therefore closes that proposed universal
  intermediate statement, not Problem XVIII itself.
- The compact finite-dimensional tracial-boundary cell is explicitly closed
  by `stw18-finite-trace-boundary-toms-winter`,
  which imports the Toms--White--Winter theorem.  This includes finitely many
  extremal traces and the unique-trace case.  Other known subclasses include
  AH algebras and crossed products of free minimal `Z^d`-actions in the cited
  STW survey.
- `stw99-xviii-implies-xxvi` records the exact conditional implication from a
  positive solution here to Winter's Cuntz-semigroup problem XXVI.
