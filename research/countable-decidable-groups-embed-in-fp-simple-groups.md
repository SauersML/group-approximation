---
rg: 2
id: countable-decidable-groups-embed-in-fp-simple-groups
kind: claim
title: Every countable group with a solvable word problem embeds in a finitely presented simple group (countable-input Boone–Higman)
distinct_from:
  boone-higman-conjecture: that is the conjecture for finitely generated inputs; this is its countable-input form, equivalent to it by the routes countable-decidable-bh-from-boone-higman and boone-higman-from-countable-decidable-bh.
  gl-n-q-embeds-in-fp-simple-group: that is one countable input; this is all countable decidable inputs, and implies it.
  countable-char-zero-linear-groups-embed-in-fp-simple-groups: that is the countable linear inputs in characteristic zero; this is every countable decidable input, and implies it.
  countable-group-embeds-in-fg-simple-kazhdan-group: that embeds countable groups in finitely generated simple Kazhdan groups, with no finite presentation; this asks for a finitely presented simple host.
---

**OPEN** (equivalent to `boone-higman-conjecture`).

**Statement.** Let `G` be a countable group with a solvable word problem. That
is, there is an enumerated generating set `s_1, s_2, …`, finite or infinite,
and an algorithm deciding which words in it represent the identity (survey
arXiv:2306.16356v3, §3.2). Then `G` embeds in a finitely presented simple group.

**Equivalence with Boone–Higman.**
- The survey's Corollary 3.5 proves this from Boone–Higman: route
  `countable-decidable-bh-from-boone-higman`.
- Conversely it contains Boone–Higman, since finitely generated groups are
  countable: route `boone-higman-from-countable-decidable-bh`.

So the countable-input form is no weaker than the conjecture. The weakenings
specific to `GL_n(Q)` are the per-input nodes:
- `sl-odd-q-has-fp-just-infinite-host`;
- `sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially`;
- `gl-n-q-in-permutational-boone-higman-class`.

**Consumers.**
- `gl-n-q-embeds-in-fp-simple-group` (route
  `gl-n-q-root-from-countable-decidable-bh`).
- `countable-char-zero-linear-groups-embed-in-fp-simple-groups` (route
  `countable-char-zero-linear-from-countable-decidable-bh`).
