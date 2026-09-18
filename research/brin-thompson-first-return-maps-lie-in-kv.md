---
rg: 2
id: brin-thompson-first-return-maps-lie-in-kv
kind: claim
title: The first-return map of an element of kV to a clopen set with bounded return times is conjugate, by a brick-local homeomorphism, to an element of kV
distinct_from:
  renormalizable-thompson-elements-give-baumslag-solitar: that uses the return map T^m on one tower level together with a brick-local conjugacy to T itself; this says any bounded-return first-return map is again an element of kV, with no relation to T required.
  odometer-factor-witnesses-mix-coordinates: that restricts candidates for an odometer factor; this is a tool for building them, by deleting locally recognizable configurations from a candidate.
---

**ESTABLISHED (2026-09-17)** through `brin-thompson-first-return-maps-lie-in-kv-proof`.
Lane proof (gq-nv-obstruct). Not independently reviewed.

**Statement.** Let `T ∈ kV`, and let `Y ⊆ C^k` be a nonempty clopen set with
`C^k = Y ∪ T^-1 Y ∪ ⋯ ∪ T^-R Y` for some `R`. Every point enters `Y` within `R`
steps. Put `r_Y(y) = min{r >= 1 : T^r y ∈ Y}` and `T_Y(y) = T^{r_Y(y)}(y)`
for `y ∈ Y`. Then:
1. `r_Y` is bounded by `R + 1` and locally constant, and `T_Y` is a
   homeomorphism of `Y`.
2. There is a brick-local homeomorphism `ψ: Y -> C^k`, meaning a finite union
   of brick-to-brick prefix replacements. For every such `ψ`,
   `ψ T_Y ψ^-1 ∈ kV`.

**Use.** A candidate for `some-brin-thompson-element-factors-onto-an-odometer`
may have the right hierarchy but inexact timing, like SMART's
`f(k+1) = 3f(k) + 4`. If its "overhead" configurations form a clopen set `O`
containing no orbit segment longer than `R`, then inducing on `Y = C^k \ O`
deletes the overhead steps. The result is again an element of `kV` up to
conjugacy. So exact timing can be sought after inducing, not only in the
machine itself.
