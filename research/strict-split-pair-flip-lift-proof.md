---
rg: 2
id: strict-split-pair-flip-lift-proof
kind: route
title: Flip licensed collisions at a factor-of-iid independent set of guard occurrences
target: strict-split-pairs-carry-positive-entropy-flip-lifts
requires:
  - split-decoders-have-generic-cantor-fibers
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

The guard lemma of `split-decoders-have-generic-cantor-fibers` licenses
replacing `v` by `u` on `hD` in `tau(z)` whenever `z` has the guard pattern on
`hW`, simultaneously over pairwise disjoint translates. Choose occurrences
equivariantly: attach i.i.d. uniform labels, and keep an occurrence when its
label is smaller than every label on `h W W^-1`. Flip each chosen occurrence on
an independent fair bit.

The resulting block map `F` is equivariant, so `nu = F_* P` is invariant, and
`sigma F = z` identically. On the event that the identity is a chosen
occurrence, which has probability `|A|^-|W| / |W W^-1|`, the identity coordinate
is a fair choice between `u(e)` and `v(e)` given the output and the labels. The
conditional entropy bound follows. Section 3 of the artifact has the full proof.
