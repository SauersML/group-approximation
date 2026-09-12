---
rg: 2
id: retained-sets-keep-component-family-uniform-fields-proof
kind: route
title: Charge retained failures to ambient failures or to images outside the retained set, then pass to uniform bounds
target: retained-sets-keep-component-family-uniform-fields
requires: []
artifacts:
  - GroupApproximation/KunThom/ComponentFamilyUniformFields.lean
---

Proved in Lean in `GroupApproximation/KunThom/ComponentFamilyUniformFields.lean`,
landed at 9d89ca20e with its root import.

- **Probe.** GREEN record `kt41-seq-wrapper.green.0912-133756-19580` (base 9346b9982,
  md5 8270c2c1e4a3f02b2f0fb703e6833483).
- **Axioms.** All six printed closures are `[propext, Classical.choice, Quot.sound]`.

1. **Preimages.** A permutation sends at most `|B|` points into `B`: its image of
   that set lies in `B` (`card_filter_apply_mem_le`).
2. **Product failures.** Let `x in V` fail the retained product law. Then either `x`
   fails the ambient law, or one of `h x`, `(g h) x`, `(g * h) x` lies outside `V`.
   Otherwise agreement rewrites both sides to the ambient values. Taking `Subtype.val`
   images and a four-fold union bound gives the count.
3. **Collisions.** If the retained labels of `t` and `t'` are equal, every `y in V`
   with both images in `V` is an ambient collision, by agreement.
4. **Uniform fields.** Combine the thresholds with `max`, using the exact count
   `|removed| + |V| = |Y|`.
   - Sizes use removed `<= |Y|/2`.
   - Multiplicativity uses removed `<= epsilon |Y| / 16` and ambient error
     `< epsilon / 4`, giving retained error `< (7/8) epsilon`.
   - Injectivity combines the finitely many pairs of `T` with `eventually_finset`.
     Collisions `<= |Y|/4` and removed `<= |Y|/8` then contradict `|Y| > 0`.
5. **Completed component labels.** At a collision of completed labels, either both
   ambient images stay in the component, where `componentCompletedAction_agrees`
   makes it an ambient collision, or one of the two elements exits.
