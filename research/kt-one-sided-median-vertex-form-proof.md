---
rg: 2
id: kt-one-sided-median-vertex-form-proof
kind: route
title: Object-vertex transfer, logarithmic observable and clamped median amplification
target: kt-one-sided-median-vertex-form
requires: []
artifacts:
  - GroupApproximation/KunThom/MedianVertexForm.lean
  - GroupApproximation/KunThom/MedianVertexFormLocal.lean
---

## Direct proof, machine-checked

- **Drift.** `drift_of_not_mem_vertexExceptional` turns the object inequality into
  one-sided drift of `f ∘ obj` along the compressor permutation off the vertex
  exceptional set. `logCut_le_add_of_mul_le` converts `(1 - ζ) a ≤ b` into an
  additive drift of at most `2ζ` for `log (max f 1)`. The proof uses
  `log x ≤ x - 1` together with `ζ ≤ 1/2`.
- **Labels.**
  - Embedded generators of `Γ` preserve the observable off the crossings of the
    `Γ`-components (`clampedLabel_negligible_of_eqOff`).
  - Compressors drift one-sidedly off the vertex exceptional set
    (`clampedLabel_negligible_of_oneSided`, through
    `sum_abs_clamped_sub_le_of_oneSided`).
  - Inverse compressors are approximate inverses (`clampedLabel_negligible_inv`,
    through `sum_abs_sub_le_of_close` and `sum_abs_sub_inv_eq`).
- **Median.** `isMedian_logCut_natMedian` transfers the natural median of `f ∘ obj`
  on every ambient component along the monotone map `t ↦ log (max t 1)`.
- **Amplification.** `deviation_negligible` gives concentration at the
  componentwise median, and `drop_negligible` gives a negligible drop set along
  the compressor.
- **Back to objects.** `card_objectVertices_failing_le` bounds the failing weight by
  the drop set plus the leak. `le_exp_mul_of_abs_logCut_sub_le` turns bounded
  logarithmic changes into ratio bounds.

Probes GREEN:
- `MedianVertexForm`: base d886a82ec, tag 0912-130712-18586;
- `MedianVertexFormLocal`: base ec41b9400, tag 0912-131953-87648.

The axiom driver at base 2b72dd6f1, tag 0912-132240-12953, prints five closures.
All five are `[propext, Classical.choice, Quot.sound]`:
- `failingWeight_negligible`;
- `localLogObservable_negligible`;
- `localRatio_negligible`;
- `card_vertexExceptional_le`;
- `card_objectVertices_failing_le`.
