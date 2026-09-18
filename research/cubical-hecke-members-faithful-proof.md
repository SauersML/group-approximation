---
rg: 2
id: cubical-hecke-members-faithful-proof
kind: route
title: The kernel is a discrete normal subgroup of the closure, so it lies in the quasi-centre; a compact open centralizing subgroup has a bounded fixed set, which each kernel element preserves, so each kernel element is elliptic, hence trivial
target: cubical-hecke-members-faithful-when-closure-fixes-bounded-sets
requires: [bs-class-with-faithful-member-lies-in-type-a-class]
---

Notation as in the target.

**Step 1 (the kernel lies in G and is normalized by the letters).** Let `K` be the
kernel of `M` on its Bass--Serre tree. Vertex stabilizers are the conjugates of
`G`, so `K` is the largest normal subgroup of `M` contained in `G`. The
assignment `g ↦ g` (`g ∈ G`), `t_i ↦ c_i` respects the HNN relations
`t_i h t_i^{-1} = φ_i(h) = c_i h c_i^{-1}` (`h ∈ G_i`), so it defines a homomorphism
`ρ: M → L` that is the identity on `G`. Since `K ⊴ M`, the subgroup
`ρ(K) = K ⊆ G` is normalized by `ρ(M) = <G, c_1, ..., c_m>`.

**Step 2 (normal in the closure).** `K ⊆ G` is discrete in `A`, hence closed. The
normalizer `N_L(K)` is closed: if `l_j → l` with `l_j ∈ N_L(K)`, then for each
`k ∈ K` the elements `l_j k l_j^{-1} ∈ K` converge to `l k l^{-1}`, which lies in the
closed set `K`; the same holds for `l^{-1}`. As `N_L(K)` contains the dense subgroup
`<G, c_i>`, it equals `L`. So `K` is a discrete normal subgroup of `L`.

**Step 3 (open centralizers).** Fix `k ∈ K`. The map `L → K`, `l ↦ l k l^{-1}` is
continuous and `K` is discrete, so the preimage `C_L(k)` of `{k}` is open. Pick a
vertex `y`. Then `U = C_L(k) ∩ L_y` is a compact open subgroup of `L` (the
stabilizer `L_y = L ∩ A_y` is compact open), and `U` fixes `y`.

**Step 4 (bounded fixed set, item 1).** Under (FB), `F = Fix_Y(U)` is a nonempty,
bounded, closed, convex subset of `Y`. Since `k` commutes with `U`,
`k F = Fix(k U k^{-1}) = F`. A bounded closed convex set in a complete CAT(0) space
has a unique circumcentre, which is therefore fixed by `k`. So `k` lies in a point
stabilizer of the discrete group `G`, which is finite because point stabilizers of
`A` are compact. `G` is torsion-free, so `k = 1`. Hence `K = 1` and `M` is faithful.

**Item 2.** Steps 1--2 hold without (FB), so `K` is always a discrete normal
subgroup of `L` contained in `G`. If `L` has none except `1` (in particular if
`QZ(L) = 1`, because Step 3 shows `K ⊆ QZ(L)`), then `K = 1`.

**Item 3.** `M` is a nontrivial member of `BS_G` acting faithfully on its tree, so
`bs-class-with-faithful-member-lies-in-type-a-class` gives `BS_G ⊆ B_A` when `G` is
finitely presented. A group acting properly and cocompactly on a CAT(0) cube
complex is finitely presented (standard for CAT(0) groups). `G` is the member with
one vertex and no edges, so `G ∈ B_A`.

**Item 4.** Edge groups have finite index, so the Bass--Serre tree `T_M` is locally
finite and `Aut(T_M)_v` is profinite. If `M` is faithful, `G = M_v` embeds in it, so
`G` is residually finite. The contrapositive, with item 1, gives item 4.

**The equivalence in (FB).** If `U` is compact open and `Fix(U)` is unbounded, it is
an unbounded closed convex subset of the proper CAT(0) space `Y`, so it contains a
geodesic ray, whose endpoint `U` fixes. Conversely, if an open subgroup `V` fixes
`ξ ∈ ∂Y`, then a compact open `U ⊆ V` fixes some `y` and `ξ`, hence the ray `[y, ξ)`
pointwise, so `Fix(U)` is unbounded.
