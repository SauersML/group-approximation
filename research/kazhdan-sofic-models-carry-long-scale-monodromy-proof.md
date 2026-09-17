---
rg: 2
id: kazhdan-sofic-models-carry-long-scale-monodromy-proof
kind: route
title: Map a van Kampen diagram into the Schreier graph along a breadth-first tree, certify the remaining edges face by face along the dual cotree, and feed the far-from-defect set to the Kazhdan rounding theorem
target: kazhdan-sofic-models-carry-long-scale-monodromy
requires:
  - kazhdan-consistent-partial-models-round-to-finite-actions
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

# Proof

Notation of the target. `Y` is the Schreier graph of `sigma`: vertex set `[n]`, and for each
`s in S` and `y in [n]` an edge from `y` to `sigma(s)y` labelled `s`. A word is read along a path
letter by letter in the order of traversal (reading right to left in the convention of
`kazhdan-consistent-partial-models-round-to-finite-actions`), with a letter `s^(-1)` meaning that
an `s`-edge is crossed backwards. With this convention a path is determined by its start and label.
Degrees in `Y` are at most `2|S|`.

## 1. Bad points

Fix `r in R` and a rotation `r'` of `r^(±1)`. The path labelled `r'` closes at `x` iff the path
labelled `r` closes at the point reached from `x` along the prefix of `r'` that precedes `r`'s
starting letter. The map from `x` to that point is a bijection of `[n]`. So `r'` fails to close at
exactly `delta_r n` points. There are at most `2|r|` choices of `r'`, so the bad set `B` has
`|B| <= eps n`.

## 2. The filling lemma

Let `w` be trivial in `G`, `rho = rho(w)`, and suppose every point of `B_Y(x, rho)` is good. Take a
van Kampen diagram `D` for `w` with base vertex `v_0` and every vertex within `rho` of `v_0` in
`D^(1)`. `D^(1)` is a finite connected plane graph with labelled oriented edges. Its bounded faces
are the 2-cells of `D`, since `D` is simply connected. The boundary walk of each bounded face,
from a suitable vertex and in a suitable direction, reads a cyclic rotation of some `r^(±1)`, and
the outer boundary walk from `v_0` reads `w`.

**Tree map.** Let `T` be a breadth-first spanning tree of `D^(1)` rooted at `v_0`, of depth
`<= rho`. For a vertex `v`, let `f(v)` be the end of the `Y`-path from `x` labelled by the label of
the `T`-path from `v_0` to `v`. Then `f(v) in B_Y(x, rho)`, so `f(v)` is good. Call an edge
`e : u -> v` labelled `s` **certified** if `sigma(s)f(u) = f(v)`. Every edge of `T` is certified.

**Cotree.** Let `Phi` be the set of faces of `D^(1)`, including the outer face `o`. For a spanning
tree `T` of a connected plane graph, the duals of the edges not in `T` form a spanning tree `T*` of
the dual graph (the tree--cotree decomposition, a standard consequence of Euler's formula and the
Jordan curve theorem). A non-tree edge has different faces on its two sides, since an edge with
the same face on both sides is a bridge and bridges lie in every spanning tree. Root `T*` at `o`.
Each bounded face `phi` has a unique parent edge `e_phi`: the non-tree edge whose dual joins `phi`
to its parent. Every other non-tree edge on the boundary of `phi` is `e_psi` for a child `psi` of
`phi`.

**Induction.** Process the bounded faces in order of decreasing depth in `T*`. When `phi` is
processed, every boundary edge other than `e_phi` is either a tree edge or `e_psi` for an
already-processed child, so it is certified. The edge `e_phi` occurs once on the boundary walk of
`phi`, because it is not a bridge. Start the boundary walk at the vertex `u` right after `e_phi`,
in the direction in which it reads a rotation `r'` of `r^(±1)`. Since `f(u)` is good, the `Y`-path
from `f(u)` labelled `r'` closes. Its first `|r| - 1` steps follow the certified edges, so after
them it is at `f(t)`, where `t` is the other end of `e_phi`. Its last step crosses `e_phi` from
`f(t)` and returns to `f(u)`. So `e_phi` is certified.

After all bounded faces are processed, every non-tree edge is `e_phi` for some bounded `phi`
(every vertex of `T*` except the root has exactly one parent edge), so every edge of `D^(1)` is
certified. Then `f` is a label-preserving map `D^(1) -> Y`. The image of the outer boundary walk
from `v_0` is the `Y`-path from `f(v_0) = x` labelled `w`, and it ends at `f(v_0) = x`. This proves
item 1.

## 3. The scale bound

Let `A = {y : d_Y(y, B) > R_0}`. Every point within distance `R_0` of `B` lies in a ball
`B_Y(b, R_0)` with `b in B`, and such a ball has at most `sum_(j <= R_0)(2|S|)^j <= 2(2|S|)^(R_0)`
points (as `2|S| >= 2`). So `eta = |[n] \ A|/n <= 2 eps (2|S|)^(R_0) < c_kappa m` by (LS1).

If `A` were consistent, item 1 of `kazhdan-consistent-partial-models-round-to-finite-actions`
would give `m <= (2 + 2/kappa^2) eta = eta/c_kappa < m`, which is absurd. So there are `x in A`
and a trivial word `w` whose path from `x` stays in `A` and does not close. If `rho(w) <= R_0`,
then `B_Y(x, rho(w)) ⊆ B_Y(x, R_0)` consists of good points (as `x in A`), and item 1 would close
the path. Hence `rho(w) > R_0`. This proves item 2.

## 4. Consequences

(C1): the largest integer `R_0` satisfying (LS1) is at least
`log(c_kappa m/(2 eps))/log(2|S|) - 1`. (C2): `titz-witzel-simple-kazhdan-cat0-lattices-exist`
gives finite presentation (a finite-index subgroup of a finitely presented group), property (T)
and simplicity for `K`, and an infinite simple group has no nontrivial finite quotient. The
remarks about local constructions in (C2) and (C3) are interpretations of item 2 and are not used
elsewhere.
