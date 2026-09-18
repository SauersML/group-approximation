---
rg: 2
id: legal-f-folded-fatgraphs-give-surface-subgroups-proof
kind: route
title: Track trees of a legal f-folded stack have one branch vertex, so the stack immerses
target: legal-f-folded-fatgraphs-give-surface-subgroups
requires: []
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/ffold.py
---

Source: Calegari--Walker, *Surface subgroups from linear programming*,
arXiv:1212.2618, TeX source `sslp.tex`. Line numbers refer to that file. Standard facts
used, not re-read at source: an immersion of connected graphs is `pi_1`-injective; a
reduced word labels a locally injective path.

**Step 0: what is reused from Calegari--Walker.** Their proof of
`proposition:f_folded_injective` (l.995--1015) has three parts.

1. A loop in the kernel of `S*_f(X) -> K` lifts to the infinite cyclic cover and lies
   in some `S_n(X) = S(X) u S(f(X)) u ... u S(f^n(X))`, mapping to `K_0^n`, which
   deformation retracts onto a copy of `R` (l.795--797, l.997--1000).
2. By (4) and `lemma:embedding` (l.927--968), `S_n(X) = S(X_n)` for the fatgraph `X_n`
   obtained by collapsing every maximal union of tracks, a *track tree*, to a point.
3. So it suffices that `X_n -> R` is an immersion. Here layer `i` is `f^i(X)`,
   subdivided so that `f^i g` is simplicial, and boundary words are not cancelled
   (l.872--878).

Parts 1 and 2 use only (4) and the `f`-fatgraph structure, not the immersion hypothesis
on `f`. Only part 3 used that hypothesis (l.996, "since ... f is an immersion ...
f^i(X) -> R is an immersion"). We re-prove part 3 from (TT), (L), (2), (3) and (4).

**Step 1: each layer immerses, and legality persists.** Take a vertex `v` of `f^i(X)`.

- *Subdivision vertex* (interior to the image of an edge of `X` labelled `x`). It is
  2-valent, and its two directions come from a turn inside the word `f^i(x)`. That word
  is reduced by (TT), so the directions differ.
- *Original vertex* of `X`. Its directions are `Df^i(d)` for the directions `d` of `v`
  in `X`. If `Df^i(d) = Df^i(d')`, then `d, d'` share a gate, so `d = d'` by (L).
  Moreover `Df^i(d)` and `Df^i(d')` lie in distinct gates whenever `d, d'` do (gates
  are `Df`-saturated).

**Step 2: the gluing graph.** Fix `n`. The track tree `T` of a vertex of `X_n` is a
tree whose nodes are vertices of the layers `f^i(X)`, `0 <= i <= n`. Each tree edge is
a gluing of a `partial^+` corner of layer `i` to a `partial^-` corner of layer `i+1`.
Write `f'` for the gluing `partial^- -> partial^+` (l.804--808). Vertices of `partial^+`
in the image of vertices of `partial^-` are the `f`-vertices (l.970--971). Refining
`f'` gives the simplicial gluing from `partial^+ S(f^i X)` to `partial^- S(f^{i+1} X)`.
Under this gluing:

- **(A)** an `f`-corner at an original vertex `u` of layer `i` is glued to a
  `partial^-` corner at an original vertex of layer `i+1`;
- **(B)** a non-`f` `partial^+` corner at an original vertex of layer `i` is glued to a
  `partial^-` corner at a *subdivision* vertex of layer `i+1` (a point interior to the
  block `f(x)`);
- **(C)** a `partial^+` corner at a subdivision vertex of layer `i` is glued to a
  `partial^-` corner at a subdivision vertex of layer `i+1`.

Every node has at most one `partial^-` corner. For original vertices this is (4). For
subdivision vertices it holds because (4) forbids an edge of `X` with `partial^-` on
both sides. So each node has at most one *downward* tree edge (the orientation of
l.955--965).

**Step 3: at most one branch node, and it is unique in its tree.** Call a node a
*branch node* if its valence in its layer is `>= 3`. A branch node is an original
vertex of `X`, and by (2) it carries no `f`-corner. Follow the tree edges out of a
branch node `u` in layer `i`.

- *Upward* edges leave through non-`f` `partial^+` corners. By (B) they reach a
  subdivision node. That node's other corner lies on the other side of the same edge of
  `X`, which is `partial^+` by (4). By (C) the chain continues upward through
  subdivision nodes, each 2-valent with one corner below and one above. So an upward
  chain never turns down and never meets a branch node.
- The *downward* edge (at most one) leaves through the `partial^-` corner of `u`. By
  (A) read backwards, it reaches an original node `v` of layer `i-1` whose corner is an
  `f`-corner. By (2) `v` is 2-valent. By (3) its other corner is not an `f`-corner, so
  it is either a `partial^-` corner or a non-`f` `partial^+` corner.
  - In the first case the chain continues downward through another 2-valent
    `f`-vertex node.
  - In the second case it turns upward into a chain as in the previous bullet.

  Either way every node reached is 2-valent.

So every tree edge path leaving a branch node meets only 2-valent nodes, and a track
tree contains at most one branch node. (A path in `T` between two branch nodes would
start by leaving the first one, and every node it then meets is 2-valent.)

**Step 4: the vertex of `X_n` has the directions of one node.** Gluing a node of
valence `k` to a 2-valent node along one corner identifies the two edge germs next to
that corner on each side. The result has valence `k + 2 - 2 = k`, and its set of
directions is the set of the `k`-valent node. Both germs of the 2-valent node are
identified with germs of the other node, and labels agree on glued boundary edges.
Build `T` by attaching nodes one at a time along tree edges. By Step 3 at most one node
is not 2-valent, so we may start from it (or from any node if all are 2-valent). The
vertex of `X_n` given by `T` then has exactly the directions of a single node. By
Step 1 those directions are pairwise distinct. So `X_n -> R` is an immersion.

**Step 5: conclusion.** By Step 0 (parts 1 and 2) and Step 4, `S_n(X)` is
`pi_1`-injective in `K_0^n` for every `n`. So `S*_f(X) -> K` is `pi_1`-injective,
component by component. `chi(S*_f(X)) = chi(S(X)) = chi(X)`, because gluing boundary
circles does not change `chi`. So if `chi(X) < 0`, some component is a closed
orientable surface of genus `>= 2` whose fundamental group injects. `QED`

**Remark (what legality replaces).** Without (L), Step 1 fails at original vertices,
because two directions of `X` in one gate eventually map to the same direction. Step 4
would then produce a non-immersed vertex of `X_n` for large `n`. Condition (TT) is what
keeps the subdivision vertices immersed. For a positive automorphism both hold for
every word `w` whose cyclic turns are legal, since `f^j(w)` is then cyclically reduced
for all `j`.
