---
rg: 2
id: rich-2to1-via-window-certified-enrichment
kind: route
title: Dead -- keep the left labels of a hard source instance and add 2-to-1 right vertices certified by bounded source windows until the matchings are rich
target: rich-2to1-games-conjecture
requires: []
---

**Dead.** The attack starts from a hard source instance `G`. It keeps the source
labels on a set `U` of variables, each with an alphabet of size `2k`. It then adds
right vertices `z` with 2-to-1 constraints on neighbour sets `S_z`, chosen
deterministically or with low entropy. The goal is pairings at each left vertex
that are uniform, or pair-uniform. Completeness is certified window by window:

* each `z` comes with a finite sub-instance `B_z` of `G`;
* every solution of `B_z` gives one common right label;
* every label at every neighbour extends to a window solution.

This generalizes `rich-2to1-via-left-preserving-local-wrappers`. It lets the
intended class be the projection of an arbitrary source window, with non-affine
sources and nonabelian coset sources.

It is killed by `window-certified-richness-is-conserved-modulo-merges`:

* Each window relation `R_(uu')` splits into forced 2-blocks and a partial
  bijection. So the wrapper's value is at least `val(Ũ_W) - phi`, where `Ũ_W` is
  an explicit unique game on `U` and `phi` is the forced edge mass. With certified
  completeness, `G -> Ũ_W(G)` is already a `Gap-UG(1 - beta - phi, s + phi)`
  reduction.
* Richness caps the forced mass by the count of distinct forced partial pairings
  the source windows derive. For `j`-block forcing, about `phi (2k)^j` of them
  are needed.
* Over coset sources on any finite group, forced vertices carry only
  central-involution translations. They have mass at most `c/((2k-1)(2k-3))`,
  and the rest is a right merge of a coset unique game.

So the route yields rich 2-to-1 hardness only where the source already supplies
either near-1 UG hardness of the derived unique game, or forced pairing families
of near-full entropy.

What survives, per the claim, is:

* windows whose forced partial pairings pass the entropy gate;
* completeness without source-local certificates;
* label re-encoding.
