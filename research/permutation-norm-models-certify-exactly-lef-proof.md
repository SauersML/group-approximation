---
rg: 2
id: permutation-norm-models-certify-exactly-lef-proof
kind: route
title: Distinct permutation matrices are one apart, so approximate means exact
target: permutation-norm-models-certify-exactly-lef
requires: []
artifacts:
  - GroupApproximation/Analysis/AmenableQuasidiagonal.lean
  - GroupApproximation/Algebra/AmenableMFProof.lean
  - GroupApproximation/Monsters/CyclicBaseLEFObstruction.lean
---

## Why sufficient

Machine-checked with no `sorry`, no axiom, and no literature premise.  The
whole thing turns on one elementary observation, and everything else is
bookkeeping around it.

**The rigidity.**  If `sigma != tau` are permutations of a finite set, pick a
point where they disagree; the corresponding basis vector is sent to two
distinct basis vectors, whose difference has `l^2` norm `sqrt 2`, and the
operator norm of `P_sigma - P_tau` is therefore at least `1`
(`one_le_l2_opNorm_permMatrix_sub`, from `permMatrix_sub_apply_of_ne`).
Contrapositively `eq_of_l2_opNorm_permMatrix_sub_lt_one`.  Since the distance
is `0` when they agree, `l2_opNorm_permMatrix_sub_eq_zero_or_one_le` is the
two-value dichotomy, and because products of permutation matrices are
permutation matrices (`permMatrix_mul_permMatrix`), the same holds for the
*multiplicativity defect* of a permutation model
(`l2_opNorm_permMatrix_defect_eq_zero_or_one_le`, with
`l2_opNorm_permMatrix_defect_eq_zero_iff` and
`perm_mul_eq_of_l2_opNorm_defect_lt_one` naming the exact case).

**Hamming buys nothing.**  A positive normalized Hamming defect means the
permutations differ somewhere, which is already the hypothesis of the rigidity
(`one_le_l2_opNorm_permMatrix_sub_of_hammingDistance_pos` and the defect
version).  `hammingDistance_lt_and_one_le_l2_opNorm_swap` and
`exists_hammingDistance_lt_and_one_le_l2_opNorm` exhibit the gap at every
accuracy with a single transposition on a large set: Hamming distance `2/card`,
operator distance at least `1`.

**The characterization.**  `isLEF_of_hasPermutationNormModels`: defect below `1`
forces exact multiplicativity on the test set
(`perm_mul_eq_of_permutationNormModel`), and an injective partial homomorphism
into a finite symmetric group is a local embedding, so the group is LEF.
Conversely `hasPermutationNormModels_of_isLEF` builds the models with defect
exactly `0` from a local embedding.  Together:
`isLEF_iff_hasPermutationNormModels`, and the contrapositive
`not_hasPermutationNormModels_of_not_isLEF`.
`isOperatorMF_of_hasPermutationNormModels` records that the class this route
does reach is MF — via LEF, i.e. via exact models.

**The manuscript's object.**  `realizedQuotient_isAmenable` gives amenability,
and `CyclicBaseLEFObstruction.realizedQuotient_not_isLEF` — already cited by
`\leanverified` in the manuscript two paragraphs after the sentence in question
— gives failure of LEF; the contrapositive yields
`realizedQuotient_isAmenable_and_not_hasPermutationNormModels`.

**The reachable positive class.**
`isAmenable_and_isOperatorMF_of_isLocallyFiniteGroup` proves both halves for
countable locally finite groups, through invariant means on one side and LEF on
the other.

## What this route deliberately does not do

It does not prove *amenable implies MF*, and no hypothesis anywhere in the
chain encodes Tikuisis--White--Winter.  The claim's content is a limitation
theorem plus an exact characterization of what the elementary route reaches;
stating the missing input rather than hiding it inside a hypothesis is the
point.
