---
rg: 2
id: translated-three-site-blocks-defeat-global-peeling
kind: claim
title: Translated three-site blocks defeat one global sparse coordinate set
distinct_from:
  three-site-pauli-refutes-unpeeled-fourth-moment: that uses one localized block to refute the little-o fourth-moment coefficient; this symmetrizes its location so no global small coordinate set catches the spikes.
  operator-tail-contraction-misses-uniform-diffuse-matching: that postulates a uniform scalar profile; this realizes such a profile as a central mixture of cheaply repairable sparse Pauli blocks.
  block-adaptive-sparse-reset-is-cheap: that positively repairs the construction using three coordinates on each central block; this proves why global rather than block-adaptive peeling is the false requirement.
---

ESTABLISHED.  Take `Theta(L)` translates of the three-site construction in
`three-site-pauli-refutes-unpeeled-fourth-moment`, arranged so that every
coordinate occurs in only `O(1)` translated triples, and form their equal
central direct sum.  The balanced energy and common raw square-function
bound remain `O(1/L)`.  The scalar anchor-odd energy is now diffuse across
the coordinates: every coordinate magnitude is `O(1/L)`.

For any global set `U=o(L)`, bounded triple incidence implies that only
`o(1)` of the central blocks have a spike coordinate in `U`.  Hence deleting
`U` leaves a `(1-o(1))` fraction of the sparse fourth-moment obstruction,
and its ratio to anchor energy remains bounded below.  Therefore the global
set formulation in
`sparse-peeling-before-anchor-fourth-moment-dichotomy` is false.

On the other hand, on each central block reset its own three coordinates.
The trace-weighted reset density is exactly `3/L`, so
`block-adaptive-sparse-reset-is-cheap` corrects the entire direct sum at
`O(1/L)` cost.  This construction is not a basin countermodel.  It proves
that layer-cake/Loewner support must be retained at least at the level of
central reducing blocks; forcing all vector states to choose one global
coordinate set loses valid cheap corrections.
