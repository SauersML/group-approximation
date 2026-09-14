---
rg: 2
id: sofic-groups-embed-in-simple-kazhdan-sofic-groups
kind: claim
title: Every finitely generated sofic group embeds in an infinite simple Kazhdan sofic group
distinct_from:
  amenable-groups-embed-in-simple-kazhdan-linear-sofic: that is proved, for amenable inputs, with linear soficity of the envelope; this asks for soficity and for all sofic inputs.
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite case, where the envelope is LEF; soficity of the input allows non-LEF groups, which no LEF envelope can contain.
  free-minimal-subshift-elementary-groups-are-sofic: that asks whether one concrete family is sofic; this asks for envelopes containing a prescribed sofic group.
---

**OPEN.** For every finitely generated sofic group `Γ` there is an infinite simple group with
property (T) that is sofic and contains `Γ`. Equivalently, the finitely generated sofic groups would
be exactly the finitely generated subgroups of infinite simple Kazhdan sofic groups, since soficity
passes to subgroups.

## Attempts

- **Cost of the statement.** It implies a sofic infinite simple Kazhdan group that is not LEF
  (`sofic-universal-envelope-forces-non-lef-simple-kazhdan`), and no such group is known.
- **Amenable inputs, rank metric.** Doubling and a free minimal subshift give an envelope that is
  simple, Kazhdan and linear sofic (`amenable-groups-embed-in-simple-kazhdan-linear-sofic`). The
  envelope is not LEF when the input is not, so the gap between the rank and Hamming metrics is the
  whole remaining content.
- **Rank to Hamming: blocked.** `gap-sofic-approximations-are-local-embeddings` shows that models of
  `EL_n(R)` through `GL_N(F_q)` on vectors, affine spaces or lines turn a rank defect `r` into a
  Hamming defect `1 - q^(-O(r))`, so they are sofic approximations only when exactly multiplicative,
  that is only when they witness LEF. The same barrier is recorded for the `Z^2` family in
  `free-minimal-subshift-elementary-groups-are-sofic`.
- **Non-amenable inputs: the Folner step fails.** The rank model above truncates the orbit
  representation to Folner sets. For a non-amenable acting group the natural replacement is a
  labelling of sofic approximation graphs by points of `X` that is equivariant off a vanishing set,
  which needs an invariant measure on `X` and a sofic orbit relation. The missing ingredient is
  recorded as `sofic-groups-have-measured-free-minimal-subshifts`.
- **Ultraproduct envelopes directly.** Inside a rank ultraproduct `∏_ω M_(N_k)(F_2)` the image of a
  sofic group is available at once, but a finitely generated simple subring with local annihilation
  containing it must still be produced, and a paradoxical one such as a Leavitt algebra is excluded
  because the rank function is stably finite. So this route returns to crossed products.
- **What would settle it.** Either a sofic approximation of some `EL_n(R)/Z` that is not a local
  embedding, which by the barrier above must avoid all algebraic targets; or a proof that a sofic
  infinite simple Kazhdan group is LEF, which would refute the statement for every non-LEF sofic
  input.
