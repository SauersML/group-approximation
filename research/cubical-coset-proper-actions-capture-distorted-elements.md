---
rg: 2
id: cubical-coset-proper-actions-capture-distorted-elements
kind: claim
title: "If a commensurating action of G has wall count proper modulo a subgroup H, then H contains a nontrivial power of every infinite-order distorted element of G"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that imports the distortion element and the Callard--Salo corollary that mV has no proper cubical action (the case H = 1); this is the relative statement for an arbitrary subgroup H, which is what constrains cubical transversal functions in a split
  haagerup-splits-as-coset-plus-subgroup-properness: that is the analytic split for arbitrary cnd functions; this shows the transversal half of the split cannot be cubical unless H absorbs powers of all distorted elements
---

**ESTABLISHED** by `cubical-coset-proper-actions-capture-distorted-elements-proof`.

**Setting.** `G` is a group acting on a set `X`, and `A ⊆ X` is *commensurated*: `gA Δ A` is
finite for every `g`. Put `ℓ(g) = |gA Δ A|`. This covers actions on CAT(0) cube complexes and
on discrete wall spaces, where the combinatorial distance `d(v, gv)` (the number of walls
separating `v` and `gv`) is `|gA Δ A|` for `X` the set of half-spaces and `A` the half-spaces
containing `v`.

`H ≤ G` is a subgroup, and `ℓ` is *proper modulo `H`* if each sublevel set `{ℓ ≤ R}` lies in
finitely many left cosets of `H`. An element `f` of infinite order is *distorted* if it lies in
a finitely generated subgroup `L ≤ G` with `|f^N|_L / N → 0`.

**Statement.**

1. (Bounded-or-linear.) For every `f ∈ G` there are an integer `m ≥ 0` and a constant `C` with
   `|ℓ(f^N) − mN| ≤ C` for all `N ≥ 0`.
2. (Capture.) If `ℓ` is proper modulo `H` and `f` is an infinite-order distorted element, then
   `f^d ∈ H` for some `d ≥ 1`.
3. (No cubical transversal.) If every infinite-order element of `H` is undistorted in every
   finitely generated subgroup of `G` containing it, and `G` has an infinite-order distorted
   element, then no commensurating action of `G` is proper modulo `H`.

Item 1 is the Haglund / Cornulier dichotomy for commensurating actions, reproved here. Item 3
with `H = 1` is Callard–Salo's Corollary 1.2 argument for `mV`.

**Use.** This is the precise obstruction killing cubical (wall, commensurated-set) constructions
of the transversal half of `haagerup-splits-as-coset-plus-subgroup-properness`, whenever the
chosen subgroup `H` is undistorted. The invariant is sublinear growth along a distorted cyclic
subgroup. Every member dies at item 1 (only linear or bounded growth) followed by the pigeonhole
in item 2, which forces a power of `f` into `H`.
