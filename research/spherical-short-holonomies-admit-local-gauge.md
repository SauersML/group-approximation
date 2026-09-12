---
rg: 2
id: spherical-short-holonomies-admit-local-gauge
kind: claim
title: Short spherical relation holonomies admit simultaneous geometrically local source-gauge trivialization
distinct_from:
  hypergraph-near-perfect-schreier-packing: that claim gives one construction of simultaneous coherent shadow maps; local-source-gauge-is-coherent-shadow-reselection proves the present claim is quantitatively equivalent to producing such maps, although not necessarily by that hypergraph.
  spherical-one-shared-map-relation-extension: that theorem handles one new relation when only one map has already been fixed; this claim is a simultaneous theorem for relation cores reusing only previously constrained maps.
  coherent-reselection-reduces-to-private-label-core: that theorem constructs the gauges outside the private-label core and proves an empty-core positive subclass; this is the still-open assertion for arbitrary nonempty cores.
  regular-character-markovization: that claim may introduce arbitrary hidden Markov states and asks only for bistochastic multiplication; this claim stays on the spherical point cloud and corrects permutations by local geometric moves.
artifacts:
  - research/artifacts/hyperlinear-cycle-synchronization-bypasses-2026-08-21.md
---

For every finite regular-character multiplication table `T` and every
`eps>0`, there are geometric and microstate tolerances with the following
property.

Start from a sufficiently accurate unitary model `{U_s}` of `T`, one
large uniform spherical cloud, and simultaneous near-perfect tight shadow
matchings for all labels, completed to total permutations `sigma_s` after
charging the completion set as exceptional.  For each tested relation
`r=(g,h,k)` let

```text
delta_r = sigma_k^(-1) sigma_g sigma_h.                 (SHG1)
```

Assume the relation holonomies move cloud points by a radius tending to zero
outside `o(N)` roots, as supplied on the matching-good/unitary-good set by
`spherical-relation-defect-pairs-small-chord` after translating output
chords back through the tight `k`-matching.

Then there exist source corrections `c_s in Sym(N)` such that

1. for every label `s`, `c_s` moves all but `o(N)` cloud points by
   spherical distance tending to zero;
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

simultaneously for all tested relations, with every `c_s` constrained to
the geometrically local permutation group of the cloud.

The content is local **cohomological stability**, not Hamming permutation
stability: the `delta_r` may be Hamming-far from the identity while moving
each affected point only a tiny geometric distance.

## Established positive region

[[coherent-reselection-reduces-to-private-label-core]] now solves the claim
whenever the table has a relation basis with empty private-label core.  More
generally it proves that every solution on the core extends to the whole
table, on the same cloud and with a table-dependent linear loss in the shadow
radius and exceptional density.

This is strictly stronger than one-overlap-forest rounding.  A relation may
reuse two assigned maps: if its third label is fresh, define that map by exact
composition or inverse composition.  Fully old closing relations also cost
nothing when they are formal consequences of the peeled basis.

A second positive region reaches a genuinely nonempty closing core.
[[finite-group-actions-have-coherent-same-cloud-shadows]] treats the complete
multiplication table of every finite group whenever the unitary colours form
an exact faithful representation, and quantitatively also any colours already
normalized-HS close to such a representation.  It constructs exact regular
orbits directly on the same iid cloud by balancing sample counts in a fine
equivariant fundamental-domain partition.  This closes the fixed near-orbit
packing gap for that subclass and does not pass through gauge equivalence.  It
does not assert that arbitrary finite-group microstates are close to exact
representations on the same Hilbert space.

Hence the live problem is confined to a **nonempty, nonredundant
private-label core** outside these exact-model-close finite-group tables.
There every remaining relation uses only labels that also occur elsewhere,
so no fresh map is available for definition and no equivariant finite action
is already available.

## Attempts

- **Repair one relation at a time.**  This is now valid throughout the peeled
  region, where a private label absorbs the repair.  It fails as a general
  core algorithm: changing an already assigned map changes every other core
  relation using that label through the conjugated term in the exact gauge
  law.
- **Use marginal Hall matchings.**  Tight single-colour Hall matchings supply
  all seed maps used by private-label peeling, but inside the core they do not
  synchronize shared copies.  A core matching theorem must impose the
  multiplication equations jointly, not only perfect marginal degrees.
- **Demand the corrections be Hamming-small.**  That throws away the new
  geometry.  A relation holonomy can move almost every index while sending
  each cloud point only a tiny geometric distance.
- **Trivialize the holonomy cohomologically.**  Unavailable.
  `spherical-displacement-length-is-not-conjugation-invariant` shows the
  cloud displacement length can inflate from zero to the full diameter under
  conjugation.  Only bounded-length conjugation paths through shadow maps
  retain quantitative control.
- **Transport the regular action along near-orbits.**  Circular.
  `orbit-transport-gauge-needs-a-closed-label-set` gives exact corrections
  at radius `5 rho+zeta` only for a closed or almost invariant label set.
  Requiring almost invariance on every group window is the Folner criterion.
- **Treat the gauges as an easier synchronization layer.**  This does not
  reduce the problem.  `local-source-gauge-is-coherent-shadow-reselection`
  proves quantitatively that a local correction family `c_s` is exactly the
  same datum as a simultaneous coherent family
  `tau_s=sigma_s c_s` which still shadows the unitary colours.  Conversely,
  any such coherent reselection gives local corrections
  `c_s=sigma_s^(-1)tau_s`.
- **Surviving attack.**  Prove a joint Hall, absorption, or local-hypergraph
  rounding theorem on every nonempty private-label core; or find a fixed
  non-amenable core table with vanishing unitary defect but a positive
  coherent-shadow radius floor.  The latter would refute the claim.
