---
rg: 2
id: kt-per-compressor-assembly-over-cluster-frames
kind: claim
title: The Lean assembly of Kun--Thom 4.1 for one compressor reduces it to four hypotheses
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Theorem 4.1 itself, imported by citation; this is the Lean assembly of its proof for one compressor, which still takes four hypotheses and so does not derive the theorem.
  kt-counting-props-producers: that proves three hypotheses of this assembly from the relative data; this is the assembly that consumes them together with frames, the joint scale choice, decompositions and words.
artifacts:
  - GroupApproximation/KunThom/CompressorNormalizationAssembly.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrame.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyThreshold.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrameSteps.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyDecomposition.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyWords.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean
---

**ESTABLISHED in Lean, as a reduction.** This is the forward direction of Kun--Thom,
arXiv:2608.06222v3, Theorem 4.1, for one compressor. Namespace
`GroupApproximation.CompressorNormalizationAssembly`.

**Statement.** Let `G` be a countable group and `Γ ≤ G` an infinite subgroup, with
`G` and `Γ` both Kazhdan. Let `C : CompressionSetup G ↥Γ PUnit` have the inclusion
as its embedding. `seqNormalizes_distinguished_of_steps` proves
`SeqNormalizes Γ C.distinguished` from four hypotheses. They are stated over:
- the decompositions `CompressorDecomposition (normalizedSetup C hembed) A`;
- the cluster frames `ClusterFrame D.retained`;
- the relative data `CountingEndgame.CompressorRelativeData C.distinguished F`.

The four hypotheses:
- **`hmatching`.** A nonnegative, vanishing `matchingError D`.
- **`hrep`.** Take a frame with repair factor `compressorRepairFactor` and a vanishing
  threshold, and a sequence `v` almost commuting with `Γ` whose `generatorDefect` is
  `o(threshold)`. Then `v` is Hamming-close to `F.patch a` for some bisection
  sequence `a`.
- **`hfunctor`.** Under the same guards, if `matchingError D` is `o(threshold)`, then
  relative data exist.
- **`hhamming`.** For relative data `M` and bisection sequences with
  `M.Transported a b`, `F.patch b` is Hamming-close to `A(t) · F.patch a · A(t)⁻¹`.

The skeleton's other hypotheses are all discharged:
- `hframe`, by the joint scale choice `exists_clusterFrame`, which gives `ρ = o(h)` by
  prescribing `√ρ`;
- `hconv`, by `ClusterFrame.almostCommutes_patch`;
- the wrapper, by `seqNormalizes_of_forall_not_uniform_lower_bound`;
- `hdecomp` and `hkazhdan`, from property `(T)`;
- `hdefect`, by `generatorDefect_vanishing`;
- `honesided`, `hmedian` and `hcounting`, by the producers of
  `kt-counting-props-producers`.

**A defect in the plan (2026-09-12): `hhamming` is false as stated.** Quantified over
`CompressorRelativeData` as landed in `7a1461b61`, it fails.
- The field `functor` records a matching `π`, a faithful morphism of restricted
  presentations and `obj_π`, and nothing ties its arrow map to `A(t)`.
- Twisting the functor by automorphisms `φ_X` of the matched objects keeps every field.
  But the lift `b` of `Transported` then approximates `t · (φ-twisted a) · t⁻¹`, not
  `t · a · t⁻¹`.
- Cluster objects have automorphisms that move a macroscopic fraction of points, for
  example the right translations of a finite quotient.
- Step 9 needs estimate (7) along the functor. This is the hypothesis `h7` of
  `BlockPatching.card_disagreement_sandwich_lt_of_lift`, and no field supplies it.

The fix is a field carrying `h7` for the distinguished compressor, with the error bound
that the near and room conditions of step 9 need. It was sent to the owners of the
relative data and of step 9. `seqNormalizes_distinguished_of_steps` needs no change,
because it passes the relative data type through unchanged.

**Two earlier corrections.**
- A partial cluster system with one uniform scale cannot carry the representation of
  almost centralizers. The frame uses per-object scales `|C| / 18`, with pair scales the
  minimum.
- Repair factor `4` does not survive transport through words for `q s q⁻¹`. The
  factor is `compressorRepairFactor = 2 (1 + |S| k) + 4`.

**What this does not give.** Until `hmatching`, `hrep`, `hfunctor` and `hhamming` are
produced, this node does not derive `kun-thom-sofic-centralizer-normalization`. Once
they are, `hasSequentialCentralizerNormalization_of_kazhdan_infranormal_of_core`
(`KunThom/NormalizationProducer`) turns the per-setup statement into normalization by
every element of `G`.

Derivation: `kt-per-compressor-assembly-over-cluster-frames-proof`.
