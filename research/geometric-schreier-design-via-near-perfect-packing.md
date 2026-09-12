---
rg: 2
id: geometric-schreier-design-via-near-perfect-packing
kind: route
title: Use a coupled near-perfect packing and complete it arbitrarily
target: geometric-schreier-design
requires:
  - spherical-near-perfect-local-package
  - hypergraph-near-perfect-schreier-packing
  - partial-schreier-completion-preserves-sofic-loss
---

The spherical package supplies the local candidate reservoirs and
quasirandomness without any exact divisibility requirement.  The packing
claim selects partial generator bijections on `1-o(1)` of the cloud with the
finite table and freeness constraints already valid there.  Complete those
partial bijections arbitrarily to permutations.  The established completion
lemma adds at most `O(L eta)` Hamming error to every tested word of bounded
length `L`, so the completed permutations form the required finite labelled
Schreier approximation.
