---
rg: 2
id: kt-per-compressor-assembly-over-cluster-frames-proof
kind: route
title: Lean proof of the per-compressor assembly of Kun--Thom 4.1 over cluster frames
target: kt-per-compressor-assembly-over-cluster-frames
requires: []
artifacts:
  - GroupApproximation/KunThom/CompressorNormalizationAssembly.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrame.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyThreshold.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyFrameSteps.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyDecomposition.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyWords.lean
  - GroupApproximation/KunThom/CompressorNormalizationAssemblyCore.lean
---

A derivation in Lean. The modules are imported by `GroupApproximation.lean`. The
Bowen–Chapman probe built them green with `-DwarningAsError=true`, under tags
0912-131722-77584, 0912-141325-36664, 0912-143243-61752, 0912-144538-31975 and
0912-145645-61789.

1. **Skeleton.** `seqNormalizes_of_compressor_of_steps` argues by contradiction.
   `seqNormalizes_of_forall_not_uniform_lower_bound` turns a failure into a uniform
   lower bound along a subsequence. For every sequence `v` that almost commutes with
   `Γ`, the steps then give:
   - a frame whose threshold dominates the generator defect and the matching error;
   - a bisection `a` with `v ≈ patch a`;
   - relative data, one-sided inequalities, concentration and a transported `b`;
   - `patch b ≈ t · patch a · t⁻¹`.

   `almostCommutes_conjSeq_of_transport` closes the argument, because `patch b`
   almost commutes with `Γ`.
2. **Frames.** `ClusterFrame R` fixes the following:
   - a positive threshold at most `min (1/100000) cheeger`;
   - a repair factor;
   - a distance between `0` and `1/5000` that vanishes;
   - a start index past which objects have scale at least `20`, with pair repair and
     pair improvement.

   `restrictFrom` removes the objects before the start, so repair holds at every
   index. The patch of a bisection almost commutes with `Γ` once the threshold
   vanishes (`ClusterFrame.almostCommutes_patch`).
3. **Joint scale choice.** `exists_clusterFrame` prescribes `√ρ` to
   `exists_joint_pairRepair`. It truncates the threshold at `min (1/100000) cheeger`
   and the distance at `1/5000`. So `ρ / threshold ≤ √ρ` from some index on, which
   gives `ρ = o(threshold)`.
4. **Decompositions.** `exists_compressorDecomposition` combines the expander
   decompositions of `KunFixedDecomposition` with a surjective enumeration of `Γ`.
   `retainedOfDecomposition` places the objects of the sequential component family.
   `generatorDefect` vanishes for almost centralizers.
5. **Words.** `exists_compressorWords` bounds the length of words for `q s q⁻¹`.
   `compressorRepairFactor` is `2 (1 + |S| k) + 4`.
6. **Concrete core.** `normalizedSetup` replaces the embedding by `Γ.subtype`, so the
   retained components live over `Γ.subtype` definitionally.
   `seqNormalizes_distinguished_of_steps` instantiates the skeleton and discharges
   `hdecomp`, `hkazhdan`, `hdefect`, `honesided`, `hmedian` and `hcounting`.
