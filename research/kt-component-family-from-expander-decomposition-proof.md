---
rg: 2
id: kt-component-family-from-expander-decomposition-proof
kind: route
title: Prune a maximal sparse cut, complete the labels, and select components at a diagonal level
target: kt-component-family-from-expander-decomposition
requires: []
artifacts:
  - GroupApproximation/KunThom/SequentialComponentFamilyPruning.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyCompletion.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyLevels.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyObjects.lean
  - GroupApproximation/KunThom/SequentialComponentFamily.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyBlocks.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyKazhdan.lean
  - GroupApproximation/KunThom/SequentialComponentFamilyCompanion.lean
---

## Direct proof, machine-checked

1. **Pruning** (`exists_prune`). Suppose every nonempty set `A` of at most half
   the points has `h |A| ≤ 2 |∂A| + B`, with `10 B ≤ h |Y|`. Take `U` of maximal
   size among the sets of at most half the points with `4 |∂U| ≤ h |U|`.
   - Then `h |U| ≤ 2 B`.
   - Let `W` be a nonempty set outside `U`, of at most half the rest, with fewer
     than `h |W| / 8` inner boundary arcs. Then `U ∪ W` is a larger sparse cut,
     or its complement `V` satisfies `h |V| < 8 B / 3` and `h |V| ≥ 4 B`. Both
     are impossible.
   - The additive bound comes from the edited expanding graph at edit distance
     `B` (`cheeger_le_two_mul_taggedBoundary_add_editDistance`).
2. **Completion** (`completion_hasCheegerLowerBound`). Inner boundary arcs are
   tagged boundary arcs of the completed labels. At most `|T|` of them share a
   directed boundary arc, so the directed Cheeger constant is `h / (8 |T|)`.
   - Completed product failures are ambient failures or one of three images in
     `U` (`card_completion_multiplicationError_le`).
   - Equal completions collide ambiently off `2 |U|` points
     (`card_sub_le_collision_add_of_completion_eq`).
3. **Levels** (`SequentialComponentFamilyLevels`). The level-`k` error of a
   component sums four families, each of negligible total:
   - product failures of the enumerated pairs below `k`;
   - label disagreements;
   - collisions of distinct labels;
   - the edit budget divided by `h`.

   A component is good at level `k` when:
   - `10 B ≤ h |C|`;
   - `(k + 1)` times its error is at most `|C|`;
   - `k < |C|`.

   A component that is not good has size at most `badBound`, whose total is
   negligible for each `k`. The diagonal level of `Matching/Selection` tends to
   infinity while the bad mass at that level stays negligible.
4. **Objects** (`SequentialComponentFamilyObjects`). On an object `5 |U| ≤ |C|`.
   - Product failures are at most `6 |C| / (k + 1)`, below `ε |C \ U|` once the
     level exceeds both enumeration indices and `10 / ε`.
   - Equal labels of two distinct elements of `T` force `|C| ≤ 6 E` with
     `10 E ≤ |C|` from level 9 on, a contradiction.
5. **Assembly** (`componentFamily`): the four fields, and the mass identity by
   splitting the component sum.

**Evidence.**
- Probe GREEN `kt41-seq-decomp.green.0912-132228-10575` for Pruning and
  Completion.
- Probe GREEN `.0912-132444-35789` for Levels (landed 9105379d6).
- Probe GREEN `.0912-133806-20204` for Objects (landed 91713c5f5).
- Probe GREEN `.0912-135143-8937` for the assembly, on base 81e3e955d. Its axiom
  driver printed 14 closures, from `exists_prune` through `componentFamily`,
  `uncoveredMass_negligible` and the mass identity. All are
  `[propext, Classical.choice, Quot.sound]`.
- Probe GREEN `.0912-141131-24405` for `SequentialComponentFamilyBlocks` and
  `SequentialComponentFamilyKazhdan`.
  - Blocks: `objectBlocks` is a `BlockPatching.BlockEmbedding`. Uncovered points
    and compatibility failures of `objectBlockAction` have negligible mass. These
    are the `huncovered` and `hcompat` hypotheses of
    `vanishing_commutator_patch_of_candidates`.
  - Kazhdan: `exists_sequentialDecompositions` and
    `exists_kazhdanPair_on_generators`.
  - All 11 printed closures are `[propext, Classical.choice, Quot.sound]`.
- Probe GREEN `.0912-142104-91891` for `SequentialComponentFamilyCompanion`.
  - Fintype instances on the object index, reachable through the family index.
  - Eventual lower bounds on object scales.
  - `objectParent` with removed mass and no-object mass negligible.
  - The retained matching of `ComponentCountingRetainedMatchingNegligible`,
    instantiated with these objects on `L.gammaDecomposition`.
  - All 13 printed closures are `[propext, Classical.choice, Quot.sound]`.

**Parallel toolkits on main, not used here.**
- `RetainedComponentExpansion` and `CentralizerNormalizationPrunedCore`: pruning
  via `MaximalCutRepair`.
- `CentralizerNormalizationUniformGood`: good components.
- `ComponentFamilyUniformFields`: field transfer to retained sets.
