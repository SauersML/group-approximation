---
rg: 2
id: hnn-cyclic-reduction-lemma
kind: claim
title: Every HNN element is conjugate into the base or to a cyclic word
distinct_from:
  hnn-torsion-theorem: That claim is the torsion-freeness conclusion; this is the word-combinatorial existence input (cyclic reduction), which has nothing to do with torsion and would also feed conjugacy and translation-length statements.
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
---

OPEN.  In an HNN extension, every element is conjugate into the base
copy or conjugate to a cyclically reduced word: formally, the interface
`HNNTorsionFree.ExistsCyclicConjugate` — every `x` is either
`g * of b * g⁻¹` or `g * c.elem φ * g⁻¹` for a `CyclicWord c`
(nonempty letter list, Britton chain condition along the word and
around the seam, head absorbed).  This is the classical
cyclic-reduction existence lemma (Lyndon--Schupp IV.2), pure word
combinatorics, independent of torsion; discharging it makes the HNN
torsion theorem ([[hnn-torsion-theorem]]) unconditional, and with it
the torsion-freeness of `ConcreteCompressionSource.integerSource`.

## Attempts

Recorded attack (2026-08-15): (i) existence of a reduced spelling for
every element — extract from Mathlib's `HNNExtension.NormalWord`
action machinery (normal words form a group action with a
product-compatible embedding; the environment's
`ReducedWord.exists_normalWord_prod_eq` converts between the two
shapes but does not by itself start from a bare element); (ii)
induction on stable-letter length: if the seam condition fails, the
word ends in a pinch `t^{-ε} a t^{ε}` against its first letter after
rotation, and conjugating by the offending prefix plus one application
of `HNNExtension.equiv_eq_conj` strictly shortens the letter list;
formalizing the rotation-conjugation bookkeeping on `ReducedWord`
products is the entire cost.  Dies today on the absence of any
product-computation API for `ReducedWord` beyond its definition;
elementary, no obstruction identified.
