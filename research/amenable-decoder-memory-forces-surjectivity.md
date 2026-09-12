---
rg: 2
id: amenable-decoder-memory-forces-surjectivity
kind: claim
title: An injective automaton with a left-inverse automaton whose memory generates an amenable group is surjective
distinct_from:
  split-decoders-have-generic-cantor-fibers: that shows a split decoder is bijective once it is pre-injective, over every group; this supplies pre-injectivity from amenability of the decoder's memory group alone, and turns it into a rule-independent filter on designs.
  sofic-groups-are-surjunctive: that needs the encoder's group to be sofic; this needs only the decoder's memory group to be amenable, while the encoder's memory group may be arbitrary.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that records a small-memory exclusion when both memories have size two; this excludes every design whose decoder memory group is amenable in the table group, any encoder memory and any rules included.
artifacts:
  - research/artifacts/table-group-holonomy-normal-form-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `amenable-decoder-memory-surjectivity-proof`.

**Theorem.** Let `tau` and `sigma` be cellular automata over any group `G` with
`sigma tau = id`. If the memory `S` of `sigma` generates an amenable subgroup, then
`tau` is surjective, and so bijective.

**Design filter.** For a design `D` and a forward-sufficient `E`, every realization
maps the decoder subgroup `Hol_S(E)` of the table group onto its decoder memory
group (`table-groups-are-memory-holonomy-groups`). So if `Hol_S(E)` is amenable, no
realization with forward table `>= E` is strict. The filter examines no rule and
no reverse product.

**Instances.**
- A decoder memory `{1, a}` never gives strictness, for any encoder memory and
  any rules.
- A strict pair needs a nonsofic encoder memory group and a nonamenable decoder
  memory group. On the decoder memory group the decoder must be a surjective,
  non-pre-injective automaton.

This is a class theorem. It decides Gottschalk's conjecture for no group.
