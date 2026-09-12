---
rg: 2
id: hnn-torsion-theorem-proof
kind: route
title: Britton powers of cyclic words, with cyclic reduction as the one interface
target: hnn-torsion-theorem
requires:
  - hnn-cyclic-reduction-lemma
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
  - GroupApproximation/GroupTheory/HNNBrittonCyclic.lean
---

## Why sufficient

Two kernel-checked halves and one named interface.

- **Britton power theorem** (`CyclicWord.elem_pow_ne_one`): a
  head-absorbed cyclically reduced word — nonempty letter list, chain
  condition along the word AND around the seam — has all powers
  spelled by literal concatenations of its letter list; the seam
  condition makes every concatenation Britton-reduced, and the
  environment's Britton lemma
  (`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`) refuses a
  nonempty reduced word in the base copy.  So cyclic words have
  infinite order.
- **Reduction** (`isPowerTorsionFree_of_existsCyclicConjugate`): if
  every element is conjugate into the base or to a cyclic word, then a
  torsion-free base gives a torsion-free extension — base conjugates
  by injectivity of `HNNExtension.of`, cyclic conjugates by the power
  theorem.
- **Grading** (`lengthHom`, `t_pow_ne_one`): the stable-letter count
  homomorphism to the integers kills no torsion off its kernel.

The formerly remaining cyclic-reduction interface is now discharged by
`HNNBritton.existsCyclicConjugate`.  The unconditional theorem
`HNNBritton.isPowerTorsionFree_hnn` applies the reduction to that witness;
`HNNBritton.isPowerTorsionFree_sourceGroup` and the integer specialization
close the affine source.  Thus this route has no open combinatorial or
literature input.
