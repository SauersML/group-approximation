---
rg: 2
id: strict-split-decoder-marker-section-proof
kind: route
title: Keep marked guard occurrences with no marked overlapping neighbour and flip them
target: strict-split-decoders-have-infinitely-many-sections
requires:
  - split-decoders-have-generic-cantor-fibers
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

The guard lemma of `split-decoders-have-generic-cantor-fibers` licenses flips on
any family of guard occurrences with pairwise disjoint windows. The marker
condition `z(hq) = a`, together with the absence of a marked occurrence at
`h delta` for `delta in W W^-1 \ {e}`, selects such a family by a local
equivariant rule. Flipping all selected occurrences gives a cellular section
different from `tau` once `q` avoids `W ∪ (W W^-1)^-1 W`, and varying `q` gives
infinitely many. Flipping on a decoration `xi` supported on the selected set
gives an injective equivariant map from the decorated subshift. Here `xi` is
recovered at each selected site, where only its own flip acts. Section 6 of the
artifact has the proof.
