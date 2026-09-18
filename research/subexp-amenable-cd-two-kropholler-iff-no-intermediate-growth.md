---
rg: 2
id: subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth
kind: claim
title: Without free subsemigroups, a finitely generated amenable cd-2 group is elementary amenable as soon as some finite-index subgroup maps onto Z; so dimension-2 Kropholler for subexponentially amenable groups is equivalent to the absence of cd-2 groups of intermediate growth
distinct_from:
  amenable-cd-two-kropholler-iff-locally-indicable: that reduces the question for all amenable groups to finite abelianization of a finitely generated counterexample, with a finite-index barrier (a Z-quotient of a finite-index subgroup does not suffice); here, in the class without free subsemigroups, a Z-quotient of any finite-index subgroup, or any infinite EA quotient, already suffices, and the question becomes a growth statement
  no-free-subsemigroups-give-fg-kernels-over-ea-quotients: that is the Rosset-type finite generation of kernels; this combines it with the cd-2 normal-subgroup theorem to classify, and with the descent through ED(X) to reduce a whole generating class
  amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar: its item 3(c) excludes infinite EA quotients by finitely generated normal subgroups; here the finite generation is automatic, so the exclusion covers every infinite EA quotient
---

**ESTABLISHED** (proposed; referee pending) through
`subexp-amenable-cd-two-kropholler-intermediate-growth-proof`.

*NFS* means: no free subsemigroup of rank two. This class is closed under subgroups and quotients.
It contains every group all of whose finitely generated subgroups have subexponential growth. A
*two-dimensional counterexample* is an amenable group of `cd_Z <= 2` that is not elementary
amenable (EA). `Kb` is the Klein-bottle group. `SG` is Grigorchuk's class of subexponentially
amenable groups: the closure under extensions and directed unions of the groups all of whose
finitely generated subgroups have subexponential growth.

1. **The NFS alternative.** Let `G ≠ 1` be finitely generated, amenable and NFS, with
   `cd G <= 2`. The following are equivalent:
   - (a) `G` is EA;
   - (b) `G ≅ Z`, `Z²` or `Kb`;
   - (c) `G` has an infinite EA quotient;
   - (d) some finite-index subgroup of `G` has infinite abelianization.

   Among the finitely generated EA groups of cd 2, which are the `BS(1,m)`, exactly those with
   `|m| >= 2` fail to be NFS.
   For a finitely generated NFS two-dimensional counterexample `K`, every finite-index subgroup
   has finite abelianization, and `K` has no infinite EA quotient.
2. **Reduction for the NFS generating class.** Every group of `cd <= 2` in
   `ED(amenable NFS)` is EA if and only if every finitely generated amenable NFS group of cd 2 is
   virtually indicable. Both directions hold.
3. **Reduction for SG.** The following are equivalent:
   - (i) every group in `SG` of `cd <= 2` is EA (Kropholler's question in dimension 2, for `SG`);
   - (ii) every nontrivial finitely generated group of subexponential growth and `cd <= 2` is
     virtually indicable;
   - (iii) no finitely generated group of intermediate growth has `cd_Z <= 2`.

   A group of intermediate growth with `cd <= 2` would also fail to be of type `FP_2`, since a
   two-dimensional counterexample is never `FP_2` (`amenable-fp-iff-affiliated-top-homology-vanishes`).

**What changed.** In the general reduction the counterexample `K` has finite abelianization,
but finite-index subgroups of `K` might map onto `Z` with kernels that are not finitely generated,
and nothing follows. Without free subsemigroups the Rosset-type theorem makes those kernels
finitely generated. Then the normal-subgroup theorem in dimension 2 applies. So for the NFS class
the target statement is "virtually indicable", which is strictly weaker than "locally indicable".
For `SG` it becomes a pure growth statement: an intermediate-growth group of cd 2.

**Scope.** Items 2 and 3 do not settle the flagship. They reduce its subexponentially amenable part
to (iii), with both directions. The standard groups of intermediate growth have infinite cd
because they have torsion or are branch groups. I found no group of intermediate growth and finite
cd in the literature I checked. Whether one exists is open, and (iii) asks it in dimension 2.
