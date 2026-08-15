---
rg: 2
id: hnn-torsion-theorem-proof
kind: route
title: Britton powers of cyclic words, with cyclic reduction as the one interface
target: hnn-torsion-theorem
requires:
  - hnn-cyclic-reduction-existence
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
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

The single remaining input is the classical cyclic-reduction existence
lemma (`ExistsCyclicConjugate`, the claim
[[hnn-cyclic-reduction-existence]]): every element is conjugate into
the base or to a cyclic word.  The affine corollaries
(`isPowerTorsionFree_sourceGroup_of_existsCyclicConjugate` and the
integer instance) consume it explicitly, so the trust surface of the
torsion theorem is exactly one combinatorial lemma wide.  Authored in
the 2026-08-15 all-fronts wave.
