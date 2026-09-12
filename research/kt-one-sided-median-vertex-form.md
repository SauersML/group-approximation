---
rg: 2
id: kt-one-sided-median-vertex-form
kind: claim
title: Vertex form of the Kun--Thom one-sided median lemma for matched Gamma-components
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1, imported by citation; this is the content of its Lemma 4.4, proved in the development for the unconditional proof of Theorem 4.1.
  kt-relative-functor-raw-map-defect-estimate: that is the finite counting behind estimate (7) of Lemma 4.3; this upgrades the one-sided orbit and isotropy inequalities of the endgame to ratios tending to 1.
artifacts:
  - GroupApproximation/KunThom/MedianVertexForm.lean
  - GroupApproximation/KunThom/MedianVertexFormLocal.lean
  - GroupApproximation/KunThom/MedianVertexFormBlocks.lean
---

**ESTABLISHED, proved here.** Modules `KunThom/MedianVertexForm` and
`KunThom/MedianVertexFormLocal`, namespace `GroupApproximation.MedianVertexForm`.

**Setting.** This is Kun--Thom, arXiv:2608.06222v3, Lemma 4.4.
- `D : LocalCriterionData G Γ J` holds a sofic approximation of `G`, the expander
  decomposition of its restriction to `Γ`, and the ambient expander decomposition
  for the labels `generatorsΓ ∪ compressors ∪ compressors⁻¹`.
- The objects are the `Γ`-components, `gammaObject D n = blockIndexOf`.
- `f n` is a natural observable of the objects, such as orbit sizes or isotropy
  orders of the cluster groupoid.
- For every compressor `q`, the map `π q n` matches objects on a domain `Dom q n`,
  and `Bad q n` is a family of exceptional objects.

**Hypotheses**, for every compressor `q`:
- `(1 - ζ n) f (π q n i) ≤ f i` for `i ∈ Dom q n \ Bad q n`, with `0 ≤ ζ n ≤ 1/2`
  and `ζ` vanishing;
- the vertices outside `Dom q n`, the vertices of `Bad q n`, and the matching leak
  `{y | obj y ∈ Dom ∧ obj (u y) ≠ π (obj y)}` along the compressor permutation
  are all `o(|Y_n|)`.

**Conclusions.**
- `localLogObservable_negligible`: for every `M > 0`, the matched components whose
  observable `log (max f 1)` changes by more than `2M` carry `o(|Y_n|)` vertices.
- `localRatio_negligible`: if `f ≥ 1`, then for every `η > 0` the matched components
  with `(1 + η) f i < f (π q n i)` or `(1 + η) f (π q n i) < f i` carry `o(|Y_n|)`
  vertices. This is equation (4) of Kun--Thom.

The generic form over any expander decomposition and any vertex-to-object map is
`failingWeight_negligible`. It keeps the clamped label hypothesis on the ambient
generators.

**Endgame form** (`MedianVertexFormBlocks.blockRatio_negligible`). This is the shape
the counting endgame consumes.
- The objects are embedded blocks `E n : BlockEmbedding (A.model n) (index n)`, and
  an object `i` weighs `|E.model i|`.
- The ambient decomposition is any expander decomposition of `A` for a symmetric
  generating set `T`. The label estimates extend from `C.ambientGenerators` to `T`
  by closure.
- **Inputs.** For every compressor `q`:
  - `f (π q n i) ≤ (1 + κ q n) f i` on `Dom q n` off a family `Bad q n` of
    negligible total weight, with `κ q` vanishing;
  - negligible weight outside `Dom q n`;
  - negligible missing source mass `Σ_{i ∈ Dom q n} sourceDefect (E.bridge (A.map n q) i (π q n i))`.

  Also negligible `E.uncovered`, and, for every embedded generator `s` of `Γ`,
  negligible `Σ_i sourceDefect (E.bridge (A.map n (embedΓ s)) i i)`.
- **Conclusion.** For `0 < η` with `2η < 1`, the objects `i ∈ Dom t n` with
  `¬ ((1 - 2η)² f (π i) ≤ (1 + 2η)² f i ∧ (1 - 2η)² f i ≤ (1 + 2η)² f (π i))` have
  negligible total weight.

## Findings

1. **Objects to vertices is a union bound.** The vertex exceptional set of an
   object inequality along `u` is the vertices outside the domain, in a bad object,
   or carried outside the matched target. `card_vertexExceptional_le` bounds it by
   the three object-level errors. `card_objectVertices_failing_le` goes back: a
   failing matched object puts each of its vertices into the drop set or the leak.
2. **A bounded observable is essential.** Kun--Thom use `H = f / (f + M_A)`, which
   is bounded, and they need no clamp. The logarithmic observable is unbounded, so
   the development clamps the centred observable to `[-M, M]`, as in
   `ComponentCountingNormalizationMedian`. Without the clamp, an exceptional set of
   density `δ / log |Y|` can carry drops of size `δ` at almost every vertex.
3. **The interface `ζ ≤ 1/2` is harmless.** Replacing a vanishing `ζ` by
   `min ζ (1/2)` keeps the clean-orbit hypothesis and its vanishing. Isotropy
   monotonicity is the case `ζ = 0`.

Derivation: `kt-one-sided-median-vertex-form-proof`.
