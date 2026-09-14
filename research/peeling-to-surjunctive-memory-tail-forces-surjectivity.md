---
rg: 2
id: peeling-to-surjunctive-memory-tail-forces-surjectivity
kind: claim
title: If an injective automaton peels to a corrected tail whose memory lies in a surjunctive subgroup, it is surjective
distinct_from:
  surjunctive-guard-subgroups-force-surjectivity: that constrains the original automaton, requiring configurations supported on unions of a surjunctive guard's cosets to stay there; this constrains the corrected tail after peeling, whose memory subgroup can be strictly smaller than the original memory group because peeling drops the peeled rows.
  surjunctivity-passes-to-subgroups: that is the plain heredity of surjunctivity to subgroups; this applies that heredity to a peeled corrected tail, combining it with own-block local-bijection peeling.
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Let `F` be an injective cellular automaton over a group `G` that peels, through
type (Z), type (O), and own-block local-bijection steps
(`own-block-local-bijection-rows-peel`), to a corrected tail `F^{(k)}` whose
local rule reads only translations by elements of a subgroup `H <= G`. If `H` is
surjunctive, then `F` is surjective.

Concrete surjunctive tails: the empty tail (no unknown left), and any tail whose
memory generates a residually finite, free, polycyclic, amenable, or sofic
subgroup, all surjunctive. The tail's memory subgroup may be a proper subgroup
of the original automaton's memory group, since peeling removes the peeled rows;
this is what makes the statement stronger than
`surjunctive-guard-subgroups-force-surjectivity`.

## Attempts

Proved in Section 2 (Theorem 2.1) of the artifact. Peeling preserves injectivity
and the surjectivity equivalence to the tail (`own-block-local-bijection-rows-peel`);
the tail's memory lies in `H`, so by `surjunctivity-passes-to-subgroups` it acts
coset by coset as an automaton over `H`, which is injective hence surjective when
`H` is surjunctive. Established by the companion route.
