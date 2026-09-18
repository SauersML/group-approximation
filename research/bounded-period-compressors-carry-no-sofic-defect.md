---
rg: 2
id: bounded-period-compressors-carry-no-sofic-defect
kind: claim
title: In a sofic group, a compressor of a Kazhdan subgroup with bounded cluster period in one sofic representation carries no compression defect, so kernel-saturating defects need wild compressors
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that kills the defect when the compressor group is Kazhdan; this kills it compressor by compressor, for arbitrary compressor groups, under a bounded cluster-period condition checked in a single sofic representation.
  compression-defects-grow-under-centralizer-closure: that kills sources whose closed core contains a Kazhdan subgroup infranormal in the kernel; this kills every source all of whose compressors are tame, with no infranormality in the kernel.
  infranormal-sources-never-saturate-sofic-mapping-tori: that kills sources infranormal in the kernel by a bead-residue central series; this is an ultraproduct criterion that ignores the bead structure.
  locally-residually-finite-targets-kill-compression-defects: that kills every compression defect in locally residually finite targets; this works inside non-residually-finite sofic groups, where compressors can permute clusters with unbounded period.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**OPEN** (it follows from `ambient-decomposition-kun-thom-normalization`, which is OPEN, and
the ESTABLISHED `bounded-cluster-period-preserves-kazhdan-fixed-algebras`).

## Statement

Let `G` be a countable sofic group, `L <= G` a Kazhdan subgroup, and
`u ∈ Comp_G(L) = { g : g L g^-1 <= L }`. Call `u` **tame** if there are:
- a sofic representation `sigma : G -> S_U` (trace zero off the identity);
- a cluster frame of `sigma|_L`;
- and `p` such that the frame satisfies `BP_p` for `u`.

By item 3 of the fixed-algebra node, this holds for example whenever `D_U^(sigma(L))` has a
frame satisfying `FD_k`. Otherwise call `u` **wild**.

1. **(Tame compressors carry no defect.)** If `u` is tame, then
   `[u c u^-1, l] = 1` for all `c ∈ C_G(L)` and `l ∈ L`.
2. **(Defect needs wildness.)** If every `u ∈ Comp_G(L)` is tame, then the intrinsic defect
   `D_G(L) = << [u c u^-1, l] : u ∈ Comp_G(L), c ∈ C_G(L), l ∈ L >>_G` of (ICD1) is trivial.
3. **(Obstruction for the extrinsic kernel.)** Consider
   `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`: a sofic `G = K ⋊ Z` with a
   Kazhdan source `L <= K` and `D_G(L) = K != 1`. Any witness needs a wild compressor `u`.
   For `u`, in **every** sofic representation of `G` and every cluster frame of `L`:
   - the dominant-target map of `u` on `L`-clusters has unbounded period on a
     non-negligible part of the mass;
   - `D_U^(sigma(L))` is infinite-dimensional.

   By `compression-defects-grow-under-centralizer-closure`, `L` may also be taken closed,
   and then the requirement is on `Comp_G(C_G L)^-1`.

**Invariant.** The *cluster period* of a compressor in a sofic representation is the
least `p` with `BP_p`, or infinity.
- **Death step.** Every member dies at the step where a finite cluster period supplies the
  expander decomposition of the `<L, u>`-graph that (KT\*) consumes.
- **Scope.** Dead are all sources whose compressors each have finite cluster period in
  some faithful sofic representation. This covers all sources with finite-dimensional fixed
  algebra in some sofic representation, whatever the compressor group.

Derivation: `bounded-period-compressors-no-defect-route`.
