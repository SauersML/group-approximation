# Proof attempt for profinite-tree-hosts-make-fa-subgroups-residually-finite (held OPEN)

This was the route `profinite-tree-hosts-fa-subgroups-rf-proof`. It was withdrawn from the graph on 2026-09-17 because two referee lenses refuted Item 3, host (E4). That step claims (E4) covers the factor-preserving lattices of `product-of-trees-lattices-satisfy-permutational-boone-higman`. Those lattices have finite stabilizers of vertices of the product, not of a single factor, so the finite-stabilizer part of Item 2 does not apply to them. See `## Attempts` in the claim. Both referees checked Step 0, Items 1 and 2, (E1)--(E3), Item 4 and Item 5 and found them correct.

Original title: Subdivide, fix a vertex, restrict to finite balls, and separate the Kac--Moody input from the tree hosts by its finite residual

Original prerequisites: `property-t-implies-property-fa`, `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, `fp-simple-kac-moody-lattices-are-mif`, `fp-simple-highly-transitive-groups-satisfy-pbh`, `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`, `aut-free-groups-satisfy-permutational-boone-higman`, `boone-higman-type-a-class-closed-under-finite-extensions`.


Notation is as in the target. A tree is a connected graph without cycles and
without multiple edges, so an automorphism is determined by its action on
vertices.

## Step 0: subdivision

Let `T_i'` be the barycentric subdivision of `T_i`. Its vertices are the vertices
of `T_i` and the midpoints of edges. `L` acts on `T_i'` without inversions, and
`T_i'` is locally finite: a midpoint has valence 2, and an old vertex keeps its
valence.

The action on the `T_i'` is faithful exactly when the action on the `T_i` is. If
`g` fixes every vertex of every `T_i'`, it fixes every vertex of every `T_i`.
Conversely, if `g` fixes every vertex of `T_i`, it fixes both endpoints of each
edge. Since there are no multiple edges, it then fixes each edge, and so each
midpoint.

## Item 1

Put `P = L_(v_1) ∩ ... ∩ L_(v_m)`. For `n >= 1` let `B_n(v_i)` be the set of
vertices at distance at most `n` from `v_i`.

- **Balls are finite.** This follows by induction on `n` from local finiteness.
- **Finite quotients.** `P` fixes `v_i` and acts by isometries, so it preserves
  each `B_n(v_i)`. This gives a homomorphism
  `rho_n : P -> Sym(B_n(v_1)) x ... x Sym(B_n(v_m))` into a finite group.
- **The kernels meet trivially.** The kernels `ker rho_n` decrease in `n`. An
  element of their intersection fixes every vertex of every `T_i`, because each
  `T_i` is connected and is the union of the balls `B_n(v_i)`. By faithfulness it
  is the identity.

So for every `1 != g in P` some `rho_n(g) != 1`, and `P` is residually finite.

## Item 2

- **A fixed vertex in each factor.** Let `H <= L` have property FA. `H` acts on
  each tree `T_i'`, so it fixes a vertex `w_i` of `T_i'`.
- **Residual finiteness.** By Step 0, `L` acts faithfully on
  `T_1', ..., T_m'`, and these trees are locally finite. By Item 1 applied to
  them, `L_(w_1) ∩ ... ∩ L_(w_m)` is residually finite. `H` is a subgroup of it,
  and subgroups of residually finite groups are residually finite.
- **Finite stabilizers.** Suppose the vertex stabilizers of `T_i` are finite. If
  `w_i` is a vertex of `T_i`, then `H <= L_(w_i)` is finite. If `w_i` is the
  midpoint of an edge `{x, y}`, then `H` permutes `{x, y}`. So the subgroup
  `H_0` fixing `x` has index at most 2 in `H`, and `H_0 <= L_x` is finite. This
  uses no faithfulness.

## Item 3

Let `H <= K` be infinite, with property FA, and not residually finite. Suppose
`K <= L` for a host `L`.

- **(E1)** `L` acts faithfully on one locally finite tree. By Item 2 with
  `m = 1`, `H` is residually finite. Contradiction.
- **(E2)** In a finite graph of groups, the valence of the vertex `gG_v` of the
  Bass--Serre tree is the sum, over the oriented edges `e` at `v`, of
  `[G_v : G_e]` (Serre, *Trees*, §I.5). With finite-index edge inclusions this
  sum is finite. So the tree is locally finite, and the action is faithful by
  hypothesis. This reduces to (E1).
- **(E3)** `L` acts faithfully on a locally finite rooted tree and fixes the
  root. By Item 1 with `m = 1` and `v_1` the root, `L` is residually finite. So
  is `H`. Contradiction.
- **(E4)** By the finite-stabilizer part of Item 2, `H` is finite.
  Contradiction.

**An infinite simple group is not residually finite.** A residually finite
nontrivial group has a proper normal subgroup of finite index. An infinite
simple group has no nontrivial finite quotient.

## Item 4

- **The input group.** By `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`,
  `S_q` is infinite, finitely presented, simple and has property (T). By
  `property-t-implies-property-fa` it has property FA. By the last paragraph of
  Item 3, it is not residually finite.
- **The inputs are admissible.** Take `A = S_q`. It embeds in a finitely presented
  simple group, namely itself.
  - The trivial subgroup is finitely generated and has decidable membership, and
    its HNN extension is `S_q * Z`.
  - `C_1 = C_2 = S_q` is finitely generated. Membership in the whole group is
    trivially decidable. Any `phi in Aut(S_q)` gives `S_q ⋊_phi Z`.
- **The HNN extension contains the input.** For any input with `S_q <= A`,
  Britton's lemma embeds `A` in `A*_phi`. So `A*_phi`, and every overgroup of it,
  contains the infinite non-residually-finite FA subgroup `S_q`.

Item 3 then excludes all hosts (E1)--(E4).

## Item 5

Let `S` be a finitely presented simple MIF group.

**Ingredients.**
- **`S_q` is MIF.** This shows `S_q` is an instance. `S_q` is a non-affine finitely presented simple Kac--Moody
  group over a finite field, as in Caprace--Rémy: its Weyl group is the
  `(2,4,6)` triangle group. By `fp-simple-kac-moody-lattices-are-mif` it is MIF.
- **`S` is in `B_A`.** By Theorem C in `fp-simple-highly-transitive-groups-satisfy-pbh`,
  `S in B_A`.
- **`Z` is in `B_A`.** By `aut-free-groups-satisfy-permutational-boone-higman`,
  `Aut(F_2)` satisfies permutational Boone--Higman. It contains the infinite
  cyclic group of inner automorphisms by a basis element. `B_A` is closed under
  subgroups by `boone-higman-type-a-class-closed-under-finite-extensions`, so
  `Z in B_A`.

**The free product.** By Corollary F in
`aut-free-groups-satisfy-permutational-boone-higman`, `B_A` is closed under free
products. So `S * Z in B_A`.

**The mapping torus.** Let `I = S ⋊_phi Z = <S, t>`, with `t` acting as
`phi`, and let `chi : I -> Z` be the projection with `chi(S) = 0`, `chi(t) = 1`.

- **Case (i): no nonzero power of `phi` is inner.** The exact sequence
  `1 -> S -> I -> Z -> 1` has finitely presented quotient `Z`. The induced map
  `Z -> Out(S)`, `n |-> [phi^n]`, is injective. By item 4 (O) of
  `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`, `I in B_A`.
- **Case (ii): some power of `phi` is inner.** Let `m >= 1` be least with
  `phi^m = ad(s_0)` for some `s_0 in S`.
  - **`phi` fixes `s_0`.** We have
    `ad(phi(s_0)) = phi ∘ ad(s_0) ∘ phi^-1 = phi^m = ad(s_0)`. An infinite simple
    group has trivial centre, so `phi(s_0) = s_0`.
  - **`z = t^m s_0^-1` is central in `I`.** For `s in S`:
    ```text
    z s z^-1 = phi^m(s_0^-1 s s_0) = s_0 (s_0^-1 s s_0) s_0^-1 = s,
    t z t^-1 = t^m phi(s_0)^-1 = z.
    ```
  - **A product of finite index.** `chi(z^k) = mk`, so `<z>` is infinite cyclic
    and meets `S` trivially. Hence `<S, z> = S x <z>`. It is the preimage
    of `mZ` under `chi`, so it has index `m` in `I`.
  - **Conclusion.** `B_A` is closed under finite direct products and finite-index
    overgroups (`boone-higman-type-a-class-closed-under-finite-extensions`,
    items 1--2). So `S x Z in B_A`, and then `I in B_A`.

**Embedding.** By item 3 of
`boone-higman-type-a-class-closed-under-finite-extensions`, every group in `B_A`
embeds in a finitely presented simple group.
