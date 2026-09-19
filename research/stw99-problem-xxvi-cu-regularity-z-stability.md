---
rg: 2
id: stw99-problem-xxvi-cu-regularity-z-stability
kind: claim
title: Cuntz semigroup Z-absorption forces Z-stability for simple nuclear algebras (STW Problem XXVI, Winter's question)
root: true
artifacts:
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

**Problem XXVI of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Winter, 2012 CBMS lectures).  If `A` is unital simple separable stably
finite nuclear with `Cu(A) ≅ Cu(A ⊗ Z)`, is `A` `Z`-stable?

Known: yes with locally finite nuclear dimension (Winter, Invent. Math.
2012; nonunital by Tikuisis).  For simple separable stably finite `A`,
STW's Proposition `prop:cu-regular` proves `Cu(A) ≅ Cu(A ⊗ Z)` ⟺
pureness ⟺ strict comparison + all ranks almost occur ⟺
`Cu(A) = V(A) ⊔ LAff_{>0}(QT(A))`; Lin (2023) adds: simple separable
finite pure algebras have stable rank one, hence pure algebras are
stably finite or purely infinite.

The compact finite-dimensional extremal-trace-boundary cell is also
positive.  `stw26-finite-trace-boundary-cu-z-stable`
extracts strict comparison from Cuntz-semigroup regularity and then applies
the finite-boundary Toms--White--Winter theorem.

## Attempts

* Two-way wiring with Toms--Winter (this session): XVIII ⟹ XXVI
  (pureness contains strict comparison), and XXVI + XXVII(1) ⟹ XVIII
  (strict comparison ⟹ pure ⟹ Cu-regular ⟹ `Z`-stable).  So modulo
  the comparison-vs-divisibility question, this problem IS the
  Toms--Winter conjecture; a counterexample here refutes Toms--Winter.
* What pureness buys beyond strict comparison: stable rank one (Lin),
  cancellation (Rieffel), all ranks almost occur, and — via the
  McDuff-type reformulation — the problem becomes: `A` pure ⟹
  `A_ω ∩ A'` pure.  Comparison transfers to the central sequence
  algebra by Matui--Sato (SI); the surviving gap is transferring
  DIVISIBILITY into `A_ω ∩ A'` without locally finite nuclear
  dimension, which is precisely Winter's step (2) and precisely
  `stw99-problem-xxviii-tracial-divisibility-gamma` territory: by CETW
  it suffices to get uniform property Γ from pureness.
