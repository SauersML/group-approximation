---
rg: 2
id: hnn-cyclic-reduction-existence
kind: claim
title: Cyclic-reduction existence for HNN extensions
distinct_from:
  greendlinger-free-product-lemma: That is the C'(1/6) small-cancellation lemma over free products; this is the elementary normal-form fact that every HNN element is conjugate into the base or to a seam-reduced word, with no metric condition.
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
---

Every element of an HNN extension is conjugate into the base copy or
conjugate to a head-absorbed cyclically reduced word (`CyclicWord`:
nonempty letter list, Britton chain condition along the word and
around the seam).  This is the classical cyclic-reduction existence
lemma; kernel-checking it would make the HNN torsion theorem
([[hnn-torsion-theorem]]) unconditional, and with it full
torsion-freeness of the routing program's integer source.

## Attempts

The natural attack is induction on the stable-letter length of a
reduced word for the element: if the first and last letters form a
pinchable seam, conjugating by the first letter shortens the word;
otherwise the word is already cyclic.  The bookkeeping lives entirely
in `HNNExtension.NormalWord.ReducedWord`; no obstruction identified,
deferred to the next wave.
