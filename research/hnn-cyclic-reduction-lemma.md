---
rg: 2
id: hnn-cyclic-reduction-lemma
kind: claim
title: Every HNN element is conjugate into the base or to a cyclic word
distinct_from:
  hnn-torsion-theorem: That claim is the torsion-freeness conclusion; this is the word-combinatorial existence input (cyclic reduction), which has nothing to do with torsion and would also feed conjugacy and translation-length statements.
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
  - GroupApproximation/GroupTheory/HNNBrittonCyclic.lean
---

ESTABLISHED and machine-checked.  In an HNN extension, every element is conjugate into the base
copy or conjugate to a cyclically reduced word: formally, the interface
`HNNTorsionFree.ExistsCyclicConjugate` — every `x` is either
`g * of b * g⁻¹` or `g * c.elem φ * g⁻¹` for a `CyclicWord c`
(nonempty letter list, Britton chain condition along the word and
around the seam, head absorbed).  This is the classical
cyclic-reduction existence lemma (Lyndon--Schupp IV.2), pure word
combinatorics, independent of torsion.  It is proved as
`HNNBritton.existsCyclicConjugate` in
`GroupApproximation/GroupTheory/HNNBrittonCyclic.lean`.  Combining it with
the Britton power theorem makes [[hnn-torsion-theorem]] unconditional and,
in particular, proves torsion-freeness of every
`ConcreteCompressionSource.SourceGroup` over a torsion-free base.

## Attempts

The completed proof first extracts a reduced spelling from Mathlib's normal
word action.  It then inducts on stable-letter length.  A bad cyclic seam is
a Britton pinch; rotating it to the interior and applying the HNN relation
strictly shortens the word.  A good seam is exactly the repository's
`CyclicWord`.  The recursion is packaged by
`HNNBritton.cyclicReduceLetters`, and the public theorem has no extra
hypotheses.
