---
rg: 2
id: kt-almost-centralizer-close-to-frame-bisection-patches
kind: claim
title: On a cluster frame a sequence with generator defect below the threshold is Hamming-close to patched total bisections
artifacts:
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationFrame.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationFrameRetained.lean
  - GroupApproximation/KunThom/CentralizerBisectionRepresentationCore.lean
distinct_from:
  kt-almost-centralizer-scaled-bisection-finite-estimates: that claim is a finite estimate at one index for one scaled cluster system; this one is the sequential statement on a cluster frame of retained components, which is the hypothesis hrep of the per-compressor assembly.
  kt-almost-centralizer-represented-by-cluster-bisection: that claim is a finite bound on the global-scale PartialClusterSystem; this one is sequential, on the scaled cluster systems of a cluster frame.
  kt-patched-bisection-commutation-vanishes-with-threshold: that claim is the converse half of Kun--Thom Lemma 4.2(4), that patched bisections almost commute with the labels; this one is the forward half, that a given sequence is close to patched bisections.
---

**ESTABLISHED in Lean.**  The forward half of Kun--Thom, arXiv:2608.06222v3,
Lemma 4.2(4), in the sequential form that the per-compressor assembly consumes.
Namespace `GroupApproximation.CompressorNormalizationAssembly`.

**Statement.**  Let `F : ClusterFrame R` be a cluster frame of retained components `R`
of a sofic approximation `A`, with `F.threshold → 0`.  Let `v n` be permutations of the
models with `generatorDefect R v n / F.threshold n → 0`.  Then some sequence of total
bisections `a n : F.Bis n` has `hammingDistance (v n) (F.patch n (a n)) → 0`.  This is
`ClusterFrame.exists_bis_patch_close_of_retained`.

It is the hypothesis `hrep` of `seqNormalizes_of_compressor_of_frameSteps` and of
`seqNormalizes_distinguished_of_steps`.  `seqNormalizes_distinguished_of_representation`
is the latter with `hrep` removed.  Its remaining hypotheses are the matching error with
`hmatching`, `hfunctor` and `hhamming`.

**How it is assembled.**
* At one index, `card_hammingDisagreement_patch_le_repBound` bounds the disagreement of
  `v n` with the patch of any bisection completing the selected arrows of `v n` by
  `ClusterFrame.repBound F v n`.  It combines the master inequality of
  `kt-almost-centralizer-scaled-bisection-finite-estimates` with the charge totals, at
  the Cheeger constant `c` of the component family.  Tagged expansion at level `c` and
  scale `1` comes from `hasTaggedExpansionAtScale_of_cheeger`.
* `repBound` is the uncovered mass, plus `(1 + 2/c)/36 · h |Y|`, plus fixed multiples of
  the uncovered, commutation and compatibility masses and of those masses over `h`.  So
  `negligible_repBound` makes it `o(|Y|)` once the masses are `o(h |Y|)` and `h → 0`.
* `ClusterFrame.exists_bis_patch_close` picks the bisections with
  `exists_bisection_selected`.
* From the start index the masses of the frame are at most those of the retained
  components.  `generatorDefect_eq_masses` writes `generatorDefect R v n` as the sum of
  the retained masses over `|Y|`.

**Why the defect must be `o(threshold)`.**  The bound divides the masses by `h`.  A block
without a candidate bridge is charged at its pair scale, and missing the thresholds
there costs only `h · scale`.

Derivation: `kt-almost-centralizer-close-to-frame-bisection-patches-proof`.
