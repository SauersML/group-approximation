---
rg: 2
id: gap-coordinates-embed-prefix-groups-in-orthant-permutations
kind: route
title: Restrict faithfully to finitely many non-u labels and use their gap coordinates
target: current-prefix-symmetry-group-is-elementary-amenable
requires: []
artifacts:
  - research/artifacts/gottschalk-prefix-symmetry-group-elementary-amenability-2026-09-08.md
---

Expand a finite generating set into primitive prefix maps,
component permutations, and mask-controlled global A_4 actions.
Choose n so the n-th non-u entry lies beyond every position these
primitives inspect or edit. Configurations with exactly n non-u
entries form N^n times a finite label set. Finite mask prefixes
give rectangular gap partitions, and the generators act there
by translations and finite label permutations.

Prove faithfulness before invoking the orthant theorem. A word
acts on the first n labels by a mask-dependent permutation and
one common A_4 multiplier; later labels get that same multiplier,
and later gaps are unchanged. If it fixes the exact-n stratum,
equal-label inputs force the multiplier to be trivial and varying
one label forces the permutation to be trivial. It therefore
fixes the dense set with at least n non-u entries, hence all inputs.

For reversible global diagonal actions selected by full component
data, use the n-th non-u label as an untouched sentinel instead.
No control sees it, so varying it forces the common multiplier to
be trivial. The same finite-rank restriction remains faithful.

The known elementary amenability of piecewise orthant-isometry
groups now applies to each finitely generated subgroup. Directed
unions prove elementary amenability of the entire current group.
The amenable Garden-of-Eden theorem excludes every full-shift
surjunctivity counterexample using addresses from this group.
