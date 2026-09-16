---
rg: 2
id: full-shift-topological-full-group-embeds-in-2v
kind: claim
title: The topological full group of the two-sided binary full shift embeds in the Brin-Thompson group 2V
distinct_from:
  topological-full-group-embeds-in-subshift-elementary-group: that puts the topological full group of a Cantor minimal system into an elementary matrix group over a crossed product; this puts the full group of the non-minimal two-sided full shift into the homeomorphism group 2V.
---

Let `X = {0,1}^Z` with shift `σ(x)_i = x_{i+1}`, and let `[[X]]` be the group of
homeomorphisms `f` of `X` with `f(x) = σ^{c(x)} x` for a continuous
`c : X → Z`. Then `[[X]]` is isomorphic to a subgroup of `2V`.

The isomorphism is conjugation by `Φ : C^2 → X`,
`Φ(a, b) = … b_1 b_0 . a_0 a_1 …`, which turns the shift into the baker's map.

**Credit.** V. Salo, *Graph and wreath products in topological full groups of
full shifts*, arXiv:2103.06663v1 (11 Mar 2021), Section 2, Lemma
"$\llb \{0,1\}^\Z \rrb \leq 2\mathrm{V}$", stated there as obvious from the
definitions. The route gives a complete proof against Brin's definition of `2V`
by dyadic subdivisions.

Route: `full-shift-topological-full-group-in-2v-proof`.
