---
rg: 2
id: embedding-in-fp-simple-groups-is-sigma-3-complete
kind: claim
title: Unconditionally, it is Sigma_3-complete to decide whether a recursively presented group embeds in a finitely presented simple group, and already whether it embeds in the single group DV_F
distinct_from:
  boone-higman-is-equality-of-two-sigma-3-index-sets: that proves the decidable index set is Sigma_3-complete and gets the same for the embeddable set only under Boone-Higman; this proves it for the embeddable set with no hypothesis.
  simple-envelope-forces-solvable-word-problem: that gives the upper containment (embeddable implies decidable); this shows the embeddable set is exactly as complex as the decidable set, so no simpler criterion characterizes it.
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that builds the host DV_F; this shows that membership of a recursively presented group in DV_F is already Sigma_3-complete.
---

**ESTABLISHED** (lane proof, not reviewed; route
`embedding-in-fp-simple-groups-is-sigma-3-complete-proof`). No priority claimed.
Index sets of this kind are standard, but this one requires the new embedding
`circulant-graph-wreath-products-embed-in-dv-f-proof`.

**Statement.** Index c.e. presentations `G_i = ⟨a, t | W_i⟩`.
1. `EMB = {i : G_i` embeds in some finitely presented simple group`}` is
   `Σ_3`-complete.
2. `EMB_{DV_F} = {i : G_i` embeds in `DV_F}` is `Σ_3`-complete. Here `DV_F` is the
   one finitely presented simple group of
   `one-fp-simple-group-contains-every-brin-thompson-subgroup`.
3. **A sharp dichotomy.** There is one computable family `i ↦ G_i` that witnesses
   both, such that:
   - if `W_i` is cofinite, `G_i ≤ DV_F`;
   - otherwise `G_i` has undecidable word problem, so it embeds in no finitely
     presented simple group.

**Consequences.**
- **No simpler test.** No property of presentations that is `Π_3` or simpler (for
  example, any `Σ_2` or `Π_2` test) characterizes the groups that embed in
  finitely presented simple groups. The same holds for the subgroups of `DV_F`.
- **Boone–Higman in this form.** It says that `EMB` equals the `Σ_3`-complete set
  `DEC`. The theorem shows both sides have the same complexity, so no
  complexity-counting argument can separate them.
