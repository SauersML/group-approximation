---
rg: 2
id: strict-automaton-tables-present-an-invisible-window-difference
kind: claim
title: The product tables of every strict automaton present a nonsofic group with an invisible Garden-of-Eden window difference
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that shows the decoder-encoder rectangle presentation must be nonsurjunctive, through surjunctive covers; this adds the Garden-of-Eden window products and places an explicit nontrivial element of the sofic radical on a window difference.
  sofic-radical-localizes-garden-of-eden-windows: that localizes the window inside the ambient memory group; this transports the localization to the finitely presented table group, so the invisibility certificate lives in the certificate's own finite tables.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `tau, sigma` be cellular automata over any group `G`, with memories `M, S`
containing `1`, `sigma tau = id`, and a Garden-of-Eden pattern `p` on a finite
window `Omega`. Let `U` be the group with generators `x_a` for `a` in
`M union S union Omega`, with `x_1 = 1`, and relators of length at most four:

    x_s x_m = x_s' x_m'  when  sm = s'm'  in G,
    x_w x_m = x_w' x_m'  when  wm = w'm'  in G.

Then some distinct `w, w'` in `Omega` have `x_w^-1 x_w'` in the sofic radical of
`U`. In particular `U` is a finitely presented nonsofic group.

The same local rules run over `U`. The decoder identity and the orphan survive,
because the relevant products have exactly `G`'s coincidences; then
`sofic-radical-localizes-garden-of-eden-windows` applies over `U`.

**Consequence.** A certificate refuting Gottschalk contains, in its own finite
product tables, a finite presentation carrying an explicit sofic-invisible
window difference. A certificate whose tables realize only a sofic
presentation cannot exist. The only presently known way to make a finite
presentation nonsofic is the one-sided compression configuration
(`openai-expander-matching-criterion`). A certificate over the Leavitt unit group
must therefore either realize such a configuration inside its decoder window, or
produce a new small nonsofic presentation as a byproduct. Proof: Section 5 of
the linked artifact.
