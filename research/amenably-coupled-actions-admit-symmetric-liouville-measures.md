---
rg: 2
id: amenably-coupled-actions-admit-symmetric-liouville-measures
kind: claim
title: A transitive action in which every finite set of points lies in one orbit of an amenable subgroup admits a non-degenerate symmetric Liouville measure, so every orbit of Thompson's F in (0,1), Thompson's T on the dyadic circle and every lamplighter action are Liouville
distinct_from:
  juschenko-zheng-liouville-actions: that imports Juschenko–Zheng's sketch-proved Lemma 2, Theorem 3 (the dyadic orbit of F) and Lemma 4 (lamplighter actions); this proves a single criterion for countable groups with symmetric measures, which recovers those and adds all F-orbits in (0,1) and Thompson's T.
  thompson-f-random-walks-are-not-liouville: that says finitely supported measures on F are not Liouville; the measures built here are infinitely supported and are Liouville only for actions, never for F itself unless F is amenable.
  thompson-f-dyadic-orbit-walks-are-transient: that says orbit walks of F on the dyadics are transient for every measure; Liouville and transient coexist, since this gives the dyadic orbit a Liouville symmetric measure, whose walk is transient by that node.
  pl-ea-calibrators-are-nonamenable-interval-groups: that shows Thompson's T acts non-amenably and non-extensively-amenably on the dyadic circle; this shows the same action is nevertheless Liouville.
---

**ESTABLISHED** through `amenably-coupled-actions-liouville-proof`.

**Setting.** `G` is a countable group acting transitively on a countable set `X`. For a probability `µ` on `G`,
`P_µ(x, y) = Σ_g µ(g)1{g·x = y}`. `(X, P_µ)` is *Liouville* if every bounded `P_µ`-harmonic function on `X` is
constant (as in `juschenko-zheng-liouville-actions`). `µ` is *non-degenerate* if `supp µ` generates `G`.

**Definition.** `G ↷ X` is *locally amenably transitive* (LAT) if every finite subset of `X` lies in a single
orbit of some amenable subgroup `H ≤ G`, where `H` may depend on the finite set. It is *locally cyclically
transitive* if `H` can always be taken cyclic.

**Theorem A.** If `G ↷ X` is LAT, then for every sequence `(g_i)` generating `G` there is a symmetric probability
`µ` on `G` with every `g_i ∈ supp µ` and `(X, P_µ)` Liouville. The measure is a convex combination of finitely
supported symmetric measures, each supported on the elements `g_i^{±1}` and an amenable subgroup.

**Corollaries.**
1. *Amenable groups.* Every transitive action of a countable amenable group is LAT (`H = G`), so it has a
   non-degenerate symmetric Liouville measure.
2. *Thompson's F.* For every orbit `Y` of `F` in `(0,1)` and every `t_1 < ⋯ < t_N` in `Y` there is `f ∈ F`
   with `f(t_i) = t_{i+1}` for `i < N`. So `F ↷ Y` is locally cyclically transitive and has a non-degenerate
   symmetric Liouville measure. For `Y` the dyadic rationals this is Juschenko–Zheng's Theorem 3; the orbits of
   irrational points are not covered by that theorem.
3. *Thompson's T.* `T ↷ D/Z`, its action on the dyadic points of the circle, is locally cyclically
   transitive, hence has a non-degenerate symmetric Liouville measure. By
   `pl-ea-calibrators-are-nonamenable-interval-groups` (item 5) this action is neither amenable nor
   extensively amenable, and `T` is a finitely generated nonamenable group.
4. *Lamplighter actions.* For every action `G ↷ X` (countable `G`, transitive), the affine action of
   `W_X = P_f(X) ⋊ G` on `P_f(X)`, `(A, g)·E = A Δ gE`, is LAT with the fixed abelian subgroup `H = P_f(X)`,
   so it has a non-degenerate symmetric Liouville measure. By
   `affine-lamplighter-amenable-iff-extensively-amenable` this action is amenable iff `G ↷ X` is extensively
   amenable. For `G = F_2` acting on itself it is a non-amenable Liouville action. For `F ↷ D` it is Liouville
   unconditionally, while its amenability is equivalent to the amenability of `F`
   (`thompson-f-amenable-iff-dyadic-action-extensively-amenable`).

**Consequence.** Liouville actions are blind to amenability, to extensive amenability, and to everything
distinguishing `F ↷ D` from `T ↷ D/Z`. The graph-level consequences for the root are drawn in
`liouville-action-criteria-cannot-decide-thompson-f-amenability`.
