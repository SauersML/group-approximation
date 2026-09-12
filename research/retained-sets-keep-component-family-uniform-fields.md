---
rg: 2
id: retained-sets-keep-component-family-uniform-fields
kind: claim
title: Removing a vanishing proportion and completing the labels keeps sizes, local multiplicativity and label injectivity uniform
distinct_from:
  kt-good-components-markov-selection: that selects good full expander components and proves the uniform bounds on their completed labels; this transfers the size, multiplicativity and injectivity fields from any full models to retained subsets, which is where the ComponentFamily producer lives once the sparse cut is removed for exact expansion.
artifacts:
  - GroupApproximation/KunThom/ComponentFamilyUniformFields.lean
---

At each index `n` let `iota n` be a finite family of objects. Each object `i`
carries:
- a finite model `Y n i`;
- labels `act n i : K -> Perm (Y n i)`;
- a retained set `V n i`;
- retained labels `ract n i : K -> Perm (V n i)` that agree with `act n i` wherever
  the image stays in `V n i`.

Suppose the removed count `|Y n i \ V n i|` is eventually at most `delta |Y n i|`,
uniformly in `i`, for every `delta > 0`.

1. **Sizes** (`size_tendsTo_subset`). If `|Y n i|` tends to infinity uniformly, so
   does `|V n i|`.
2. **Local multiplicativity** (`locallyMultiplicative_subset`). If
   `d_H(act(gh), act(g) act(h))` tends to zero uniformly for each fixed pair, so does
   `d_H(ract(gh), ract(g) ract(h))`. The underlying count is at most the ambient
   failures plus three times the removed count
   (`card_hammingDisagreement_subset_mul_le`).
3. **Injective labels** (`labelsInjective_subset`). Let `T` be finite. Suppose
   ambient labels of distinct elements of `T` eventually collide on at most a
   quarter of each model, and the models are eventually nonempty. Then the retained
   labels are eventually injective on `T`. Equal retained labels force
   `|V| <= collisions + 2 |removed|` (`card_le_collision_add_of_subset_eq`).

For completed labels on an expander component, the collisions of two completed
labels are at most the ambient collisions plus the exits of both elements
(`card_componentCompletedAction_collision_le`). With the collision and exit counts
of `kt-good-components-markov-selection` this gives hypothesis 3.

The statements do not depend on how `V` is chosen. They apply both to the
maximal-cut retained set of `RetainedComponentExpansion` and to the pruning of
lane kt41-seq-decomp. Injectivity on the full components does not imply
injectivity on retained sets; the collision counts are needed.

Derivation: `retained-sets-keep-component-family-uniform-fields-proof`.
