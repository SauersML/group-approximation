---
rg: 2
id: amalgam-torsion-permanence-needs-no-cyclic-reduction-proof
kind: route
title: Induct on syllable length over normal words, contradicting the cyclically reduced branch
target: amalgam-torsion-permanence-needs-no-cyclic-reduction
requires: []
artifacts:
  - GroupApproximation/Algebra/PushoutITorsionFree.lean
  - GroupApproximation/Higman/TorsionFreeImageClosure.lean
---

Machine-checked.  Three moves over `Monoid.PushoutI.NormalWord`, the amalgam
analogue of the repository's free-product argument.

**A nonempty word avoiding the base is nontrivial.**  Mathlib's
`Monoid.PushoutI.Reduced.eq_empty_of_mem_range` is the Britton analogue, and
every normal word is of that kind because a transversal meets the base only in
`1` (`reduced_toWord`).

**A cyclically reduced such word has no trivial power.**  Its `n`-fold
concatenation is again such a word --- the letters are unchanged and the chain
condition survives each junction because the two ends lie in different factors
--- so `pow_ne_one_of_cyclicallyReduced`.

**Cyclic reduction, only where needed.**  `exists_conj_into_factor_aux` inducts
on the number of non-base syllables.  The amalgam differs from the free product
in that a normal word carries a base element in front of the letters, so the
induction absorbs that element into the first letter before conjugating.  When
the last letter lies in a different factor the conjugate is cyclically reduced
and the previous step contradicts the finite-order hypothesis; otherwise the
conjugate is shorter and the induction applies.

Hence `exists_conj_into_factor`, and torsion-freeness follows factor by factor.
`Amalgam.isPowerTorsionFree_push` reads this at the repository's two-element
diagram, `TorsionFreeBenignWitness.mapEmb` glues it onto the benign witness, and
`Seq.torsionFreeImageClosure` is the named input, discharged.

## Why the deleted gate is not recoverable here

The cyclically reduced word appears in this argument only inside a branch that
is immediately contradicted.  To inhabit the universal statement one would have
to return it instead, and in the branch where the merged letter falls into the
base there is nothing to return until the base element has been transported
through the remaining letters.  That transport is the content of the amalgam
normal-form theory, not a corollary of this induction, which is why deleting
the gate was the correct move rather than a concession.
