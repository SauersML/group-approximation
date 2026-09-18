---
rg: 2
id: irreducible-jnc-tree-lattices-pbh-via-bader-shalom
kind: route
title: Unimodularity rules out fixed ends and abelian normal subgroups of the closures, Bader--Shalom then makes every projection injective, and a faithful factor finishes
target: irreducible-tree-lattices-with-jnc-closures-are-pbh
requires: [bader-shalom-normal-subgroup-theorem, product-of-trees-lattices-with-faithful-factor-satisfy-pbh, tree-lattices-split-into-irreducible-blocks, product-of-two-trees-lattices-satisfy-permutational-boone-higman, burger-mozes-infinitely-transitive-tree-groups]
---

Notation as in the target. `Ḡ = Ḡ_1 x ... x Ḡ_n`.

**Step 0 (Γ_0 is a lattice in Ḡ with dense projections).** The diagonal map
`Γ_0 -> Ḡ` is injective because `Γ` is faithful on `X`, and its image is
discrete because `Γ_0` is discrete in `∏ Aut(T_i)`. `Ḡ` acts on `X` with compact
open vertex stabilizers, and `Γ_0` has finitely many vertex orbits. So for a base
vertex `x_0`, every `g ∈ Ḡ` has `g x_0 = γ y` with `γ ∈ Γ_0` and `y` in a finite
set `F`. Then `γ^(-1) g` lies in the compact set `{h : h x_0 ∈ F}`, so `Γ_0` is
cocompact. The projection to each `Ḡ_i` is dense by definition. Each `Ḡ_i` is
locally compact and compactly generated: it acts on the connected locally finite
graph `T_i` with compact open stabilizers and finitely many orbits.

**Step 1 (unimodularity).** A locally compact group containing a lattice is
unimodular, and the modular function of `Ḡ` is the product of those of the
`Ḡ_i`. So every `Ḡ_i` is unimodular. For a compact open subgroup `K` and `g`,
unimodularity gives `[K : K ∩ gKg^(-1)] = [gKg^(-1) : K ∩ gKg^(-1)]`.

**Step 2 (item 1, no fixed end).** Let `G = Ḡ_i` be non-discrete and suppose it
fixes an end `ξ`.
- *A hyperbolic element exists.* If every element were elliptic, `G` would
  preserve every horosphere of `ξ`. Finitely many vertex orbits would then meet
  finitely many horospheres, which is impossible because the Busemann function is
  unbounded on `T_i`. So let `h ∈ G` be hyperbolic, translating towards `ξ`, and
  `v` a vertex on its axis `A`.
- *Stabilizers along the axis.* `G_v` fixes `v` and `ξ`, hence the ray `[v, ξ)`,
  which contains `hv`. So `G_v ⊆ G_(hv) = h G_v h^(-1)`, and Step 1 forces
  equality. Hence `G_(h^m v) = G_v` for every `m`.
- *All stabilizers inside `G_v`.* For any vertex `w`, the ray `[w, ξ)` shares a
  tail with `A`, so it contains a vertex `a` of the axis. Then
  `G_w ⊆ G_a = G_v`.
- *Contradiction.* For `g ∈ G`, `G_(gv) = g G_v g^(-1) ⊆ G_v`, and Step 1 gives
  equality. So `G_v` fixes the orbit `Gv` pointwise. That orbit is coarsely dense,
  and in a leafless tree its convex hull is the whole tree (as in Step 2 of
  `tree-lattice-block-splitting-proof`). So `G_v` is trivial and `G` is discrete,
  a contradiction.

**Step 3 (item 1, no abelian normal subgroup).** Let `B ⊴ G = Ḡ_i` be abelian.
- If `B` has a hyperbolic element `b`, then for `g ∈ G` the hyperbolic element
  `gbg^(-1) ∈ B` commutes with `b`. Commuting hyperbolic automorphisms of a tree
  have the same axis. So `g · Axis(b) = Axis(b)`, and by minimality `T_i` is a
  line, contrary to the hypothesis of more than two ends.
- Otherwise every element of `B` is elliptic. A group of elliptic automorphisms of
  a tree has a fixed point in the geometric realization or fixes a unique end
  (standard, not re-read). A unique fixed end would be fixed by `G`, which Step 2
  excludes. Otherwise `Fix(B)` is a nonempty closed convex `G`-invariant set. It
  is unbounded, since `G` has unbounded orbits, so it contains a vertex, and its
  vertices span a `G`-invariant subtree. By minimality that subtree is `T_i`, so
  `B = 1`.

**Step 4 (item 2).** Assume `Γ` is irreducible and each `Ḡ_i` is
just-non-compact. Irreducibility makes each `pr_i(Γ_0)`, hence each `Ḡ_i`,
non-discrete, and for `n > 3` it makes every projection to `∏_(i ≠ j) Ḡ_i`
non-discrete. With Steps 0–3, every hypothesis of
`bader-shalom-normal-subgroup-theorem` holds. Its conclusions: `Γ_0` is
just-infinite and every projection `Γ_0 -> Ḡ_j` is injective. So `Γ_0` acts
faithfully on `T_j`, and item 3 of
`product-of-trees-lattices-with-faithful-factor-satisfy-pbh` gives `Γ ∈ B_A`.

**Step 5 (items 3 and 4).** Item 3: blocks on one or two trees are in `B_A` by
item 3 of `tree-lattices-split-into-irreducible-blocks`. Blocks on at least three
trees are irreducible faithful lattices with just-non-compact closures by
hypothesis, so they are in `B_A` by Step 4, and item 3 of the block claim
assembles `Γ`. Item 4: for `n = 3`, a reducible `Γ` splits into blocks on one and
two trees and lies in `B_A`. An irreducible `Γ` with all closures
just-non-compact lies in `B_A` by Step 4, and its closures are all non-discrete.

**Trust surface.** Bader--Shalom via Caprace's survey (imported node); the
elliptic-subgroup trichotomy; commuting hyperbolic automorphisms share an axis.
The Burger--Mozes sufficient condition is only quoted, and no result depends on
it.
