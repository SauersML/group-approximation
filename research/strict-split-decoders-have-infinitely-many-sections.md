---
rg: 2
id: strict-split-decoders-have-infinitely-many-sections
kind: claim
title: A decoder with a strict cellular section has infinitely many cellular sections and embeds a decorated shift
distinct_from:
  split-decoders-have-generic-cantor-fibers: that packs guard occurrences by an external choice and embeds Cantor sets into single fibers; this chooses packing centers by a cellular marker rule, producing new cellular sections and an equivariant injection of a decorated subshift into the full shift.
  strict-split-pairs-carry-positive-entropy-flip-lifts: that selects occurrences with i.i.d. labels and flips on fair coins to build an invariant measure; this uses only the configuration itself, so every construction is a cellular map.
artifacts:
  - research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md
---

Let `G` be infinite, and let `tau, sigma` be cellular automata on `A^G` with
`sigma tau = id` and `tau sigma != id`. Then:

1. `sigma` has infinitely many distinct cellular sections. A bijective `sigma`
   has exactly one.
2. There are a closed invariant subshift
   `Y ⊆ (A x {0,1})^G` with `A^G x {0} ⊊ Y` and an injective equivariant
   continuous `Phi : Y -> A^G` with `Phi(z, 0) = tau(z)` and
   `sigma Phi(z, xi) = z`.

The marker rule keeps a guard occurrence `h` when a marker symbol sits at `hq`,
and no overlapping occurrence also carries its marker. The kept occurrences are
pairwise disjoint and are chosen by a cellular rule. Flipping all of them gives
a new section. Flipping those with `xi(h) = 1` gives `Phi`, and `xi` is read back
from the flipped sites. Full proof: Section 6 of the artifact.

So the number of cellular sections separates strict pairs (infinitely many)
from bijective decoders (one). Over an amenable group, (2) contradicts
monotonicity of topological entropy. Over a general group no monotone invariant
is known, and the embedding is invisible on constant configurations.
