---
rg: 2
id: word-problem-solvability-rec2-sigma3-proof
kind: route
title: The shift family's word problem is the index set's membership problem
target: word-problem-solvability-rec2-is-sigma3-complete
requires:
  - shift-raag-family-classifies-amenability
---

**Upper bound.**  "Some total program decides equality of words in the
presented group": `exists e', forall w, [phi_{e'}(w) halts and phi_{e'}(w)
= 1 iff w = 1 in G]`; the bracket is a Boolean combination of a
`Sigma^0_1` halting statement and the r.e. word problem, hence
`Delta^0_2`, so the whole is `Sigma^0_3`.

**Reduction.**  Let `J_e = {j + 1 : j in W_e}` and `G_e = G_{J_e}` as in
[[shift-raag-family-classifies-amenability]]; the presentation is
recursive uniformly in `e`.  If `W_e` is recursive, so is `J_e`; a word
`w` in `a^{+-1}, t^{+-1}` of length `L` rewrites effectively as `u t^k`
with `u` a word in `a_i`, `|i| <= L`, and `w = 1` iff `k = 0` and `u = 1`
in the right-angled Artin group on the window `{a_i : |i| <= L}`, whose
edges are decided by `J_e`; the word problem of a finite right-angled
Artin group given by its graph is decidable (normal forms by shuffling
and cancellation).  So the word problem of `G_e` is decidable.
Conversely, from a decision procedure for the word problem of `G_e`,
decide `j in J_e` by asking whether `[a, t^j a t^-j] = 1`: in a
right-angled Artin group two generators commute iff they are adjacent, so
this holds iff `j in J_e`.  Thus `{e : G_e has solvable word problem} =
{e : W_e recursive} = REC`, `Sigma^0_3`-complete by Rogers' theorem.
