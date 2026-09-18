---
rg: 2
id: cubulated-pointed-cube-category-proof
kind: route
title: Last-edge hyperplanes pairwise cross, a hyperplane crossed twice forces a last-edge hyperplane crossed twice, and the median of o, go and gω cuts a common tail off the two rays
target: cubulated-groups-act-by-bisections-of-a-pointed-cube-category
---

Standard facts used, not re-read at source: hyperplanes of a CAT(0) cube complex
separate it into two convex halfspaces; two hyperplanes cross iff all four quarter
spaces are nonempty; vertices are the consistent DCC ultrafilters on halfspaces (and
Roller points the consistent non-principal ones); all combinatorial geodesics between
two vertices are related by square flips; pairwise adjacent-and-crossing edges at a
vertex span a cube (flag condition).

**Item 1.** Let `H_1, H_2 ∈ Max(x, y)`, with dual edges `(y, y_1)`, `(y, y_2)`. Then
`y ∈ H_1^+ ∩ H_2^+`, `x ∈ H_1^- ∩ H_2^-`, `y_1 ∈ H_1^- ∩ H_2^+`, `y_2 ∈ H_1^+ ∩ H_2^-`.
All four quarter spaces are nonempty, so `H_1, H_2` cross. The ultrafilter of `y` with
both choices flipped is consistent (every pair of its halfspaces meets, because the
pairs occur in `y`, `y_1`, `y_2`, or are `H_1^-, H_2^-`), so the two edges span a
square at `y`. By the flag condition all of `Max(x, y)` spans a cube.

**Key lemma.** If `H` separates `y` from both `x` and `z`, then some hyperplane in
`Max(x, y) ∩ Max(z, y)` does too. If `H` is adjacent to `y` take it. Otherwise let `K`
be the hyperplane dual to the first edge of a geodesic from `y` to the carrier `N(H)`.
Then `K` is adjacent to `y`, separates `y` from `N(H)`, and is disjoint from `H` (a
hyperplane meeting `H` meets `N(H)`). So `H ⊆ K^-` and the halfspace of `H` not
containing `y` lies in `K^-`. It contains `x` and `z`, so `K ∈ Max(x, y) ∩ Max(z, y)`.

**Item 2.** The first claim is the key lemma, since the converse direction is trivial.
For the update: `Max(y, z) ⊆ Max(x, z)` because `H(y, z) ⊆ H(x, z)`, and
`H ∈ Max(x, y)` adjacent to `z` does not separate `y, z` (geodesic), so separates `z`
from `x`. Conversely let `H ∈ Max(x, z) \ H(y, z)`; it separates `y` from `x`. If it
were not adjacent to `y`, the key lemma applied to `y`, `x` and a vertex of `N(H)`
on `z`'s side would give `K ∈ Max(x, y)` separating `y` from `N(H) ∋ z`, so
`K ∈ H(x, y) ∩ H(y, z)`, contradicting geodesicity.

**Item 3.** With `x = x_κ`, `Max(x_κ, y) = κ` (the hyperplanes of `κ` separate `y` from
`x_κ` and are adjacent to `y`, and no others separate them). Given composable
`(y, κ, z)` and `(z, κ', w)` with `κ' = κ(x_κ, z)`, item 2 applied at `z` shows
`x_κ → z → w` is geodesic, so `x_κ → y → z → w` is geodesic and `(y, κ, w)` is a
morphism with source `[(w, κ(x_κ, w))]`, consistent with the source of `(z, κ', w)`
(item 2 again). Associativity and identities are clear. Freeness of the action on
vertices makes orbits of triples with a fixed range representative correspond to
their far vertices, which gives both cancellations. Finitely many objects:
cocompactness and local finiteness. The factorization into `S` is the Niblo--Reeves
normal cube path, which is geodesic and a sequence of cubes each admissible for the
state left by the previous ones (item 2).

**Item 4.** For `ω ∈ ∂_R X`, `H(o, ω)` with its nesting order is an infinite heap;
finite order ideals are the `H(o, z)` for vertices `z` on geodesics from `o` toward
`ω`, which gives the bijection. Fix `g`. Let `z' = m(o, go, gω)`, the median; its
ultrafilter chooses for each hyperplane the halfspace containing two of the three
points. Then `H(o, gω) = H(o, z') ⊔ H(z', gω)` and `H(go, gω) = H(go, z') ⊔ H(z', gω)`,
so `g[o, ω)` and `[o, gω)` share the tail `[z', gω)`. Its translate `g^{-1}[z', gω)` is
the tail of `[o, ω)` after `g^{-1}z'`. The prefixes `[o, z']` and `[o, g^{-1}z']` depend
only on which hyperplanes of the finite set `H(o, go)` separate `o` from `gω`, a
clopen condition. The source objects match once the states agree, i.e. once
`Max(o, z'') = Max(go, z'')` for the vertex `z''` reached on the common tail. These
differ only by hyperplanes of `H(o, go)` adjacent to `z''`. For `ω ∈ R` the tail leaves
the carriers of these finitely many hyperplanes, so a suitable `z''` exists. Take the cylinder of paths extending `[o, g^{-1}z'']` and remove the finitely many
subcylinders of paths that cross a hyperplane of `H(o, g^{-1}o)` not crossed by
`[o, g^{-1}z'']` (finitely many minimal extensions each, since two vertices have at
most one join). On this compact open neighbourhood of `ω` every point has the same
median data and the same tail split, so `g` is `λw ↦ μw` with `λ`, `μ` the orbits of
`[o, g^{-1}z'']` and `[o, z'']` from the base object.

**Lesson for general BH.** The key lemma (a hyperplane crossed twice forces a
last-edge hyperplane crossed twice) is the whole reason the state is finite. It is
the cube-complex analogue of "no backtracking" in trees, and it is what any
normal-form host for a group with flats must reproduce.
