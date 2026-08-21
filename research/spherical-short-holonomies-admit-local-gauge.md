---
rg: 2
id: spherical-short-holonomies-admit-local-gauge
kind: claim
title: Short spherical relation holonomies admit simultaneous geometrically local source-gauge trivialization
distinct_from:
  hypergraph-near-perfect-schreier-packing: that claim couples the initial matching choices so relations hold on most roots; this claim fixes an already selected tight permutation table and asks for geometrically local source corrections solving its finite holonomy system.
  spherical-one-shared-map-relation-extension: that theorem handles one new relation when only one map has already been fixed; this claim is a simultaneous theorem for cyclic relations reusing multiple fixed maps.
  regular-character-markovization: that claim may introduce arbitrary hidden Markov states and asks only for bistochastic multiplication; this claim stays on the spherical point cloud and corrects permutations by local geometric moves.
artifacts:
  - research/artifacts/hyperlinear-cycle-synchronization-bypasses-2026-08-21.md
---

For every finite regular-character multiplication table `T` and every
`eps>0`, there are geometric and microstate tolerances with the following
property.

Start from a sufficiently accurate unitary model `{U_s}` of `T`, one large
uniform spherical cloud, and simultaneous near-perfect tight shadow matchings
for all labels, completed to total permutations `sigma_s` after charging the
completion set as exceptional.  For each tested relation `r=(g,h,k)` let

```text
delta_r = sigma_k^(-1) sigma_g sigma_h.                 (SHG1)
```

Assume the relation holonomies move cloud points by a radius tending to zero
outside `o(N)` roots, as supplied on the matching-good/unitary-good set by
`spherical-relation-defect-pairs-small-chord` after translating output chords
back through the tight `k`-matching.

Then there exist source corrections `c_s in Sym(N)` such that

1. for every label `s`, `c_s` moves all but `o(N)` cloud points by spherical
   distance tending to zero;
2. the corrected maps `tilde_sigma_s=sigma_s c_s` satisfy every tested
   multiplication relation on all but `eps N` roots; and
3. all correction, matching-domain, and relation exceptional sets have total
   density below `eps` after the tolerances are chosen sufficiently small.

Equivalently, up to the charged exceptional roots, the corrections solve the
finite nonabelian system

```text
c_k = delta_(g,h,k)
      (sigma_h^(-1)c_g sigma_h)c_h                     (SHG2)
```

simultaneously for all tested relations, with every `c_s` constrained to the
geometrically local permutation group of the cloud.

The content is local **cohomological stability**, not Hamming permutation
stability: the `delta_r` may be Hamming-far from the identity while moving
each affected point only a tiny geometric distance.