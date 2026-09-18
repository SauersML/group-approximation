---
rg: 2
id: pspace-fp-simple-via-lift-presented-automaton-overgroups
kind: route
title: Put a PSPACE-complete Wächter–Weiß group in a lift-presented automaton group, take the simple commutator host, and cap it at PSPACE
target: fp-simple-group-with-pspace-complete-word-problem
requires:
  - automaton-groups-embed-in-lift-presented-automaton-groups
  - lift-presented-automaton-groups-satisfy-boone-higman
  - automaton-tail-full-groups-have-conp-relative-word-problem
  - finite-commutator-wachter-weiss-groups-are-not-fp
---

1. **A PSPACE-complete input.** Take finite `R`, for example `A_5`, acting off the encoding letters,
   and the Wächter–Weiß automaton group `G_R`. By `finite-commutator-wachter-weiss-groups-are-not-fp`
   (item 4), its finitely generated subgroup `H_R` has PSPACE-complete word problem.
2. **A lift-presented overgroup.** By `automaton-groups-embed-in-lift-presented-automaton-groups`,
   `G_R` embeds in an automaton group `G' <= Aut(X'^*)` whose relator kernel is a finitely generated
   lift ideal.
3. **The host.** By `lift-presented-automaton-groups-satisfy-boone-higman`, `G'` embeds in the simple
   group `S = [V, V]` with `V = V_{md}(G')` for the regrouped action on `T_{md}`. `S` has finite index
   in `V` and is finitely presented. The regrouped action is still finite-state, since reading `m`
   letters at a time preserves finiteness of the state set.
4. **Lower bound.** `H_R <= G_R <= S`. By the length-linear substitution, the word problem of `S` over
   any finite generating set is PSPACE-hard.
5. **Upper bound.** `S` is a finitely generated subgroup of `V_{md}(G') = FV(G')` (one coordinate), and
   `G'` is an automaton group. By `automaton-tail-full-groups-have-conp-relative-word-problem`,
   items 1–2, `WP(S) ∈ coNP^{WP(G')} ⊆ coNP^{PSPACE} = PSPACE`.

So `S` is a finitely presented simple group with PSPACE-complete word problem. `∎`

**Narrowest premise.** Step 2 is used for the single group `G_R`, and for one `R`. A lift-presented
automaton overgroup of any Wächter–Weiß group suffices. That includes the binary headline group, with
Aleshin's `F_3` as `R`, whose hardness is the paper's theorem as stated. Its own action is the first
candidate. For finite `R` this needs `V_2(C)` finitely presented
(`lift-presentation-passes-to-invariant-subalphabets`, application).
