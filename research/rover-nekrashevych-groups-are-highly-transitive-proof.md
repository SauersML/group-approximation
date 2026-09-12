---
rg: 2
id: rover-nekrashevych-groups-are-highly-transitive-proof
kind: route
title: Glue sections on small cones and match the complements by a prefix replacement, then pass to normal subgroups by density in Sym(N)
target: rover-nekrashevych-groups-are-highly-transitive
requires: []
---

Notation as in the claim. A clopen set `Y <= C` is a finite disjoint union of
cones. Splitting one cone `uC` into the `d` cones `uxC` raises the count by
`d - 1`, and any two cone decompositions of `Y` have a common refinement. So
the number of cones in a decomposition of `Y`, taken mod `d - 1`, is an
invariant `c(Y)`. It is additive on disjoint unions, and `c(C) = 1`.

**Step 0: fullness.** Suppose `C = P_1 ⊔ ... ⊔ P_r = Q_1 ⊔ ... ⊔ Q_r` are clopen
partitions, and `h: C -> C` maps each `P_j` onto `Q_j` by the restriction of
some element of `V_d(G)`. Then `h` is in `V_d(G)`.
- Refine each `P_j` into cones on which the chosen element has the form
  `u w -> v g(w)`.
- On a subcone `uaC`, with `a` a word, the same element reads
  `u a w -> v g(a) g|_a(w)`, and `g|_a` is in `G` by self-similarity.
- So `h` has the defining form on a cone partition, and it is a bijection.

**Step 1: orbits.** `V_d(G)` is countable, because `G` is and each element is
given by finite data. So `O` is countable.
- `O` contains the `V_d`-orbit of any of its points `x = vw`: all points `uw`
  with `u` a word. That set is infinite and dense in `C`.
- An element acting trivially on `O` is a continuous map fixing a dense set, so
  it is the identity. The action on `O` is faithful.

**Step 2: high transitivity.** Let `x_1, ..., x_k` be distinct points of `O`, and
`y_1, ..., y_k` distinct points of `O`. Choose `h_i in V_d(G)` with
`h_i(x_i) = y_i`.
- Each `h_i` has the form `u w -> v g(w)` on some cone containing `x_i`. By
  Step 0 it keeps that form on every smaller cone around `x_i`. Let `u_i` be the
  prefix of `x_i` of length `L`; then `h_i(u_i w) = v_i g_i(w)`, where `v_i` is
  a prefix of `y_i` whose length grows with `L`.
- Take `L` so large that the `u_i` are distinct, the `v_i` are pairwise
  incomparable, and neither `U = ⊔ u_i C` nor `W = ⊔ v_i C` is all of `C`.
  This is possible because the `x_i` are distinct and the `y_i` are distinct.
- The complements `P = C \ U` and `P' = C \ W` are nonempty clopen sets, and
  `c(P) = 1 - k = c(P')`. Subdivide cones until `P` and `P'` are unions of the
  same number `a` of cones, say `P = ⊔ p_j C` and `P' = ⊔ q_j C`.
- Define `h` by `h(u_i w) = v_i g_i(w)` and `h(p_j w) = q_j w`. It maps a cone
  partition of `C` bijectively onto a cone partition of `C`, so `h` is in
  `V_d(G)` and `h(x_i) = y_i` for every `i`.

So the action on `O` is `k`-transitive for every `k`.

**Step 3: normal subgroups.** Give `Sym(O)` the topology of pointwise
convergence. A subgroup of `Sym(O)` acts highly transitively exactly when it is
dense. Let `rho: V_d(G) -> Sym(O)` be the faithful action, with dense image by
Step 2, and let `N` be a nontrivial normal subgroup of `V_d(G)`.
- Conjugation is continuous, so the closure `M` of `rho(N)` is normalized by
  `rho(V_d(G))`.
- The normalizer of a closed subgroup is closed: if `g_n -> g` and every
  `g_n M g_n^-1 <= M`, then `g m g^-1 = lim g_n m g_n^-1` lies in `M`.
- So `M` is normalized by the closure of `rho(V_d(G))`, which is `Sym(O)`.
  Hence `M` is a nontrivial normal subgroup of `Sym(O)`, where `O` is
  countably infinite.
- By Schreier--Ulam (1933) and Baer (1934), every nontrivial normal subgroup of
  `Sym(O)` contains the finitary alternating group `Alt_fin(O)`.
- `Alt_fin(O)` is dense. A finite partial injection extends to a permutation of
  a larger finite set, and if that permutation is odd, compose it with a
  transposition of two points outside its domain and range.
- Therefore `M = Sym(O)`, so `N` acts highly transitively on `O`. It acts
  faithfully because it is a subgroup.

Finally, `[V_d(G), V_d(G)]` is nontrivial: it contains the commutators of the
Higman--Thompson group `V_d <= V_d(G)`, which is not abelian. ∎
