# Common-retract amalgams in the permutational Boone--Higman class, and even Artin groups (2026-09-16)

Lane: swarm, target `boone-higman-conjecture`, angle "special case / strengthening"
(agent `hi-spec-boone-higman-conjecture`). This artifact holds the derivations
behind:

- `pbh-class-closed-under-common-retract-amalgams` (route
  `pbh-common-retract-amalgam-closure-proof`);
- `artin-pbh-reduces-to-odd-component-cliques` (route
  `artin-pbh-odd-component-reduction-proof`);
- `even-fc-artin-groups-satisfy-permutational-boone-higman` (route
  `even-fc-artin-pbh-via-clique-reduction`).

Not independently reviewed.

## 0. Summary and what is new

`B_A` is the class of groups that embed in a group admitting an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`). Every member embeds in
a finitely presented simple group and, if finitely generated, has solvable word
problem (`type-a-action-gives-boone-higman-for-subgroups`).

**Theorem A (common-retract amalgams).** Let `X, Y ∈ B_A` and let `C` be a common
subgroup that is a retract of `X` and a retract of `Y`. Then `X *_C Y ∈ B_A`.

- **A1 (trees of groups).** Take a finite tree of groups whose vertex groups lie in
  `B_A`, where every edge group is a retract of both adjacent vertex groups. Its
  fundamental group lies in `B_A`.
- **A2 (equivariant graph products).** Let `Γ` be a finite nonempty simplicial
  graph with vertex groups `G_v`. Let a group `C` act on each `G_v` by automorphisms,
  so that `C` acts on the graph product `G_Γ` preserving every vertex group. If
  `G_v ⋊ C ∈ B_A` for every `v`, then `G_Γ ⋊ C ∈ B_A`.

**Theorem B (Artin groups: odd-component reduction).** Let `Γ` be a finite labelled
graph with Artin group `A_Γ`. Call the connected components of the subgraph formed by
the odd-labelled edges (isolated vertices included) the *odd components*. Let `Q` be
the graph whose vertices are the odd components, two of them joined when some edge of
`Γ` joins them. Then `A_Γ ∈ B_A` if and only if `A_{Γ[S]} ∈ B_A` for every union `S`
of the odd components in a clique of `Q`.

**Corollary C (even Artin groups).** If all finite labels of `Γ` are even, then
`A_Γ ∈ B_A` iff `A_Δ ∈ B_A` for every clique `Δ` of `Γ`.

**Corollary D.** Let `Γ` be even, and suppose that in every clique `Δ` each connected
component of the subgraph of label-`≥ 4` edges is a vertex, an edge, or a path of two
edges both labelled 4. Then `A_Γ ∈ B_A`. So `A_Γ` embeds in a finitely presented
simple group. This includes **every even Artin group of FC type**.

**What is new.**

1. Theorem A strictly contains Part 1 of `pbh-class-closed-under-graph-products`,
   which is the case `Y = C × K`. That node's Scope lists the twisted case
   `X *_C (K ⋊ C)` as not covered. The new input is to realize both factors inside
   one simple MIF envelope through the fibre product `X ×_C Y`, and to send `M` to
   transvections rather than to a commuting set. A2 contains Part 2 of that node
   (`C = 1`).
2. Corollary D is, as far as the bounded search of §8 found, the first Boone--Higman
   (or permutational Boone--Higman) theorem for even Artin groups beyond
   right-angled, spherical, Euclidean, and forest-defined ones.
   - The labelled 4-cycle `a -4- b -4- c -4- d -4- a` is an example.
   - It is not virtually cocompactly cubulated, by Huang--Jankiewicz--Przytycki
     Theorem 1.1 (§8), so the linearity route through virtual specialness is not
     available from the cubulation literature.
   - Its star splittings are twisted, so Part 1 of the graph-product node does not
     apply: `A(a -4- b -4- d)` is not `<b, d> × K`.
3. Theorem B is the `B_A` analogue of the word-problem transfer
   `artin-word-problem-reduces-to-free-of-infinity-graphs` (Godelle--Paris). That
   transfer holds for every graph, because an algorithm only needs membership in
   parabolic subgroups. `B_A` needs retractions, and these exist exactly across
   even edges, so the reduction units are the odd-saturated cliques of `Q`.

## 1. Imports and conventions

Automorphisms compose right to left. The imports:

- (I1) `boone-higman-type-a-class-closed-under-finite-extensions`: `B_A` is closed
  under subgroups and finite direct products (Zaremsky, arXiv:2405.18354,
  Proposition 5.5).
- (I2) `fp-simple-highly-transitive-groups-satisfy-pbh`: BFFHZ Theorem C,
  (i) ⟹ (iv). A finitely generated group with a type (A) action embeds in a
  finitely presented simple MIF group.
- (I3) `relative-automorphism-of-fp-simple-mif-group-has-type-a-action`: BFFHZ
  Theorem E. For `H` finitely presented simple MIF and `n ≥ 2`, the group
  `Aut_H(H * F_n)` of automorphisms fixing `H` pointwise admits an action of type (A).
- (I4) `type-a-action-gives-boone-higman-for-subgroups`: Zaremsky Corollary B.

## 2. Proof of Theorem A

Let `r_X: X -> C` and `r_Y: Y -> C` be retractions. Put `L = ker r_X` and
`M = ker r_Y`, so `X = L ⋊ C` and `Y = M ⋊ C` internally. Write `c·l = c l c^-1`
(computed in `X`) and `c·m = c m c^-1` (computed in `Y`). Let `G = X *_C Y`.

### Step 0. Structure of `G`

- `r_X` and `r_Y` agree on `C` (both are the identity there). So they glue to a
  homomorphism `R: G -> C` with `R|_C = id`. Hence `G = ker R ⋊ C`.
- Put `N = <L, M> <= G`. `G` is generated by `L`, `M` and `C`. `N` is normalized by
  `L` and `M`, and by `C` because `C` normalizes `L` in `X` and `M` in `Y`. So `N` is
  normal, and `G = N C`.
- `N <= ker R` and `ker R ∩ C = 1`. By the modular law,
  `ker R = N (ker R ∩ C) = N`. So `G = N ⋊ C`.
- **`N ≅ L * M`.** Take a reduced alternating product `g_1 ⋯ g_k`, `k ≥ 1`, of
  nontrivial elements of `L` and `M`. Since `L ∩ C = 1 = M ∩ C`, the factors lie
  alternately in `X \ C` and `Y \ C`. By the normal form theorem for amalgamated
  free products the product is nontrivial. So the natural map `L * M -> N` is
  injective, and it is onto.

So `G ≅ (L * M) ⋊ C`, with `C` acting on `L` and on `M` through `X` and `Y`.

### Step 1. One simple MIF envelope for both factors: the fibre product

Let `D = X ×_C Y = {(x, y) ∈ X × Y : r_X(x) = r_Y(y)}`.

- `D` contains the three subgroups `L' = L × 1`, `M' = 1 × M` and
  `C' = {(c, c) : c ∈ C}`.
- `(c, c)(l, 1)(c, c)^-1 = (c·l, 1)` and `(c, c)(1, m)(c, c)^-1 = (1, c·m)`. So
  inside `D`, conjugation by `C'` induces on `L'` and `M'` exactly the actions from
  `X` and `Y`.

Choose groups `Γ_X ⊇ X` and `Γ_Y ⊇ Y` with type (A) actions. `Γ_X × Γ_Y` is finitely
presented and carries a type (A) action (I1). By (I2) it embeds in a finitely
presented simple MIF group `H`, and so does its subgroup `D`. Identify `L`, `M`, `C`
with `L'`, `M'`, `C'` inside `H`. Then:

```text
c l c^-1 = c·l  and  c m c^-1 = c·m  in H, for c ∈ C, l ∈ L, m ∈ M.        (F)
```

Nothing is assumed about `L ∩ M` or `[L, M]` inside `H`. In fact `L'` and `M'`
commute, and the proof never uses this.

### Step 2. The actor and two families of automorphisms

Put `P = H * F(x, y)` and `Ω = Aut_H(P)`. By (I3) with `n = 2`, `Ω` has a type (A)
action, so every subgroup of `Ω` lies in `B_A`.

- **Transvections.** For `a ∈ H * <y>` let `ρ_a` fix `H` and `y` and send
  `x -> x a`.
  - `ρ_a ρ_b(x) = ρ_a(x b) = x a b`, since `ρ_a` fixes `b`. So `ρ_a ρ_b = ρ_(ab)`,
    and `a -> ρ_a` is a homomorphism `H * <y> -> Ω`.
  - It is injective, since `ρ_a(x) = x a`.
- **Twisted conjugations.** For `c ∈ H` let `γ_c` fix `H` and send `x -> x c`,
  `y -> c^-1 y c`.
  - `γ_c γ_d(x) = x c d` and `γ_c γ_d(y) = (cd)^-1 y (cd)`. So `c -> γ_c` is a
    homomorphism `H -> Ω`.
  - Each `γ_c` preserves `H * <y>`.
- **Conjugation formula.** For `a ∈ H * <y>` and `c ∈ H`:

  ```text
  γ_c ρ_a γ_c^-1 = ρ_(c γ_c(a) c^-1).                                    (GP1)
  ```

  - On `x`: `x -> x c^-1 -> x a c^-1 -> x c γ_c(a) c^-1`.
  - On `y`: `y -> c y c^-1`, which `ρ_a` fixes, and `γ_c` sends it back to `y`.
  - `H` is fixed throughout.

  This is (GP1) of `pbh-graph-product-closure-proof`.

### Step 3. The homomorphism

Let `w: L * M -> H * <y>` be the homomorphism with `l -> y l y^-1` and `m -> m`.
Define `Φ_N = ρ ∘ w: L * M -> Ω` and `Φ_C = γ|_C: C -> Ω`.

**The semidirect product relation.** We need
`Φ_C(c) Φ_N(n) Φ_C(c)^-1 = Φ_N(c·n)` for all `n ∈ L * M`.

- By (GP1) the left side is `ρ_(c γ_c(w(n)) c^-1)`.
- `n -> c γ_c(w(n)) c^-1` and `n -> w(c·n)` are homomorphisms `L * M -> H * <y>`,
  so it suffices to compare them on generators.
- **On `l ∈ L`.** `γ_c(y l y^-1) = c^-1 y c l c^-1 y^-1 c`, since `γ_c` fixes `l`.
  So `c γ_c(y l y^-1) c^-1 = y (c l c^-1) y^-1`, which is `y (c·l) y^-1 = w(c·l)` by
  (F).
- **On `m ∈ M`.** `c γ_c(m) c^-1 = c m c^-1 = c·m = w(c·m)` by (F).

So `Φ = (Φ_N, Φ_C)` is a homomorphism `G = (L * M) ⋊ C -> Ω`.

### Step 4. Injectivity

- **`w` is injective.** Take a reduced word `g_1 ⋯ g_k`, `k ≥ 1`, alternating
  between `L \ 1` and `M \ 1`.
  - Its image is obtained by writing each `L`-syllable `l` as `y · l · y^-1` and
    keeping each `M`-syllable `m`. For example `l_1 m_1 l_2` goes to
    `y · l_1 · y^-1 · m_1 · y · l_2 · y^-1`.
  - Two `y`-letters are never adjacent, because two `L`-syllables are separated by an
    `M`-syllable. Two `H`-letters are never adjacent, because every `L`-letter sits
    between `y` and `y^-1`.
  - Every `H`-letter is nontrivial, because `L -> D -> H` and `M -> D -> H` are
    injective.
  - So the image is a reduced alternating word in `H * <y>` of length at least one,
    hence nontrivial.
- **`Φ` is injective.** Suppose `Φ(n c) = ρ_(w(n)) γ_c = id`, with `n ∈ L * M` and
  `c ∈ C`.
  - Evaluate on `y`: `γ_c(y) = c^-1 y c`, and `ρ_(w(n))` fixes it. So
    `c^-1 y c = y` in `H * <y>`.
  - A nontrivial element of `H` does not commute with `y` in a free product, so
    `c = 1`.
  - Then `ρ_(w(n)) = id`, so `w(n) = 1`, and `n = 1`.

Hence `G ≅ Φ(G) <= Ω`, and `G ∈ B_A`. ∎

**Remark (why the fibre product).** For `Y = C × K` one may take the envelope of
`K × X`, because `M = K` commutes with `C`. In the twisted case `C` must act on `L` and
on `M` through the same copy of `C`. The fibre product is the smallest group in
which this happens with `L` and `M` embedded. It lies in `B_A` because it is a
subgroup of `X × Y`, and no amalgam is formed there.

## 3. Trees of groups (A1)

Let `T` be a finite tree with vertex groups `G_u`, edge groups `C_e` and injections
`C_e -> G_u` at each end. Suppose that for every edge `e = {u, v}` there are
retractions `r_(u,e): G_u -> C_e` and `r_(v,e): G_v -> C_e`. For a subtree `S` let
`G_S` be the fundamental group of the restricted tree of groups. It is an iterated
amalgam, and each `G_u` with `u ∈ S` embeds in it.

**Lemma 3.1.** For every subtree `S` and every vertex `v ∈ S`, `G_v` is a retract of
`G_S`.

*Proof.* Induct on `|S|`; `|S| = 1` is trivial. Otherwise write `S = S' ∪ {w}`, with
`w` a leaf of `S` joined by `f = {w, z}` to `z ∈ S'` and `v ∈ S'`. By induction there
is a retraction `ψ: G_S' -> G_v`. Now `G_S = G_S' *_(C_f) G_w`. Define the map to be
`ψ` on `G_S'` and `ψ ∘ r_(w,f)` on `G_w`. The two agree on `C_f`, since `r_(w,f)` is
the identity there. So they glue to a homomorphism `G_S -> G_v` extending `ψ`. It is
the identity on `G_v`. (A tree with at least two vertices has at least two leaves,
so a leaf `w ≠ v` exists.) ∎

**Proof of A1.** Induct on the number of vertices. Choose a leaf `u` joined by `e`
to `v`, and let `T' = T \ u`. Then `G_T = G_T' *_(C_e) G_u`.

- `C_e` is a retract of `G_u` by hypothesis.
- It is also a retract of `G_T'`: compose a retraction `G_T' -> G_v` (Lemma 3.1) with
  `r_(v,e)`.
- `G_T' ∈ B_A` by induction, and `G_u ∈ B_A`.

Theorem A gives `G_T ∈ B_A`. ∎

## 4. Equivariant graph products (A2)

Let `Γ` be a finite nonempty simplicial graph, `G_v` groups, and `α_v: C -> Aut(G_v)`
actions of one group `C`. The defining relators of the graph product `G_Γ` are the
relators of the `G_v` and the commutators `[g, h]` with `g ∈ G_u`, `h ∈ G_v`, `uv` an
edge. The `α_v` preserve them, so `C` acts on `G_Γ` preserving each `G_v`. For an
induced subgraph `Λ`, the subgroup `G_Λ` is `C`-invariant.

**Lemma 4.1.**

- (a) **Retractions.** For an induced subgraph `Λ <= Γ`, killing every `G_u` with
  `u ∉ Λ` defines a `C`-equivariant retraction `π_Λ: G_Γ -> G_Λ`. Hence
  `(g, c) -> (π_Λ(g), c)` is a retraction `G_Γ ⋊ C -> G_Λ ⋊ C`.
- (b) **Splitting.** For a vertex `v`,
  `G_Γ ⋊ C = (G_(Γ \ v) ⋊ C) *_(G_(lk v) ⋊ C) (G_(st v) ⋊ C)`.
- (c) **Stars.** `G_(st v) ⋊ C = (G_(lk v) × G_v) ⋊ C` embeds in
  `(G_(lk v) ⋊ C) × (G_v ⋊ C)` by `(g h, c) -> ((g, c), (h, c))`.

*Proof.*

- (a) Every relator goes to a relator or to 1. The composite with `G_Λ -> G_Γ` is the
  identity on generators. Equivariance holds on each `G_u`, both sides being `c·g` or
  `1`.
- (b) First, `G_Γ = G_(Γ \ v) *_(G_(lk v)) G_(st v)`. The two presentations have the
  same generators and relators, since every commutator relator involving `v` lives in
  `st v`. The maps from `G_(lk v)` are injective by (a).
  - For an amalgam `A *_B A'` on which `C` acts preserving `A`, `A'` and `B`, one has
    `(A *_B A') ⋊ C = (A ⋊ C) *_(B ⋊ C) (A' ⋊ C)`. Both sides are generated by `A`,
    `A'` and `C`, subject to the relations of `A`, `A'` and `C`, the identification of
    `B`, and `c g c^-1 = c·g` for `g ∈ A ∪ A'`. The last family implies the same
    relation for all `g ∈ A *_B A'`.
  - `B ⋊ C` is a subgroup of both factors, since `B` embeds in `A` and `A'`.
- (c) A direct computation: `(g h, c)(g' h', c') = (g (c·g') · h (c·h'), c c')`,
  using that `G_(lk v)` and `G_v` commute. The map is injective because
  `(g, c) = (1, 1)` and `(h, c) = (1, 1)` force `g h = 1` and `c = 1`. ∎

**Proof of A2.** Induct on `|V(Γ)|`. If `Γ = {v}`, the hypothesis is the conclusion.
Otherwise pick any vertex `v`.

- `X = G_(Γ \ v) ⋊ C ∈ B_A` by induction.
- `Y = G_(st v) ⋊ C ∈ B_A` by Lemma 4.1(c) and (I1). Here `G_(lk v) ⋊ C ∈ B_A` by
  induction when `lk v ≠ ∅`. When `lk v = ∅` it is `C <= G_v ⋊ C`.
- `G_(lk v) ⋊ C` is a retract of `X` and of `Y` by Lemma 4.1(a). For `Y`, kill `G_v`.

Theorem A and Lemma 4.1(b) give `G_Γ ⋊ C ∈ B_A`. ∎

**Examples.**

- `C = 1` recovers Part 2 of `pbh-class-closed-under-graph-products`.
- Let every `G_v = Z^2`, and let `C = Z` act at each vertex by some `A_v ∈ SL_2(Z)`.
  - Each `Z^2 ⋊_(A_v) Z` embeds in `GL_3(Z)` by `(u, n) -> [[A_v^n, u], [0, 1]]`, so it
    lies in `B_A` (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
  - Hence the mapping torus `A_Γ' ⋊ Z` lies in `B_A`. Here `A_Γ'` is the right-angled
    Artin group of the graph `Γ'` obtained by doubling every vertex (the graph product
    of copies of `Z^2`), and `Z` acts by the vertex-wise automorphism `(A_v)_v`.
  - When some `A_v` is hyperbolic, `Z^2 ⋊_(A_v) Z` is a Sol lattice and a subgroup of
    the mapping torus (Lemma 4.1(a)). By the solvable subgroup theorem
    (Bridson--Haefliger II.7.8, recalled, not re-read) the mapping torus is then not a
    CAT(0) group. So the graph's CAT(0) route (`cat0-groups-satisfy-boone-higman`,
    open) would not reach it even if completed.
  - Linearity of such mapping tori was not searched here.

## 5. Artin groups: retractions, splittings, Theorem B

**Conventions.**

- `Γ` is a finite simplicial graph with vertex set `V`, and every edge `uv` carries
  a label `m_uv ∈ {2, 3, 4, ...}`. A non-edge means `m_uv = ∞`.
- `A_Γ = < V | Π(u, v; m_uv) = Π(v, u; m_uv) for every edge uv >`, where `Π(u, v; m)`
  is the alternating word `u v u ⋯` of length `m`.
- For `S ⊆ V`, `A_S` denotes the Artin group of the induced labelled subgraph
  `Γ[S]`.
- The *odd components* are the connected components of the graph `(V, odd edges)`;
  isolated vertices count as components.
- `S` is *odd-saturated* when it is a union of odd components. Equivalently, no
  odd-labelled edge joins `S` to `V \ S`.
- `Q` is the graph on the odd components, with `O ~ O'` when some edge of `Γ` joins
  `O` to `O'`.

**Lemma 5.1 (even-boundary retractions).** Let `Λ ⊆ V`, and suppose every edge
joining `Λ` to `V \ Λ` has even label. Then `π_Λ: A_Γ -> A_Λ`, with `u -> u` for
`u ∈ Λ` and `u -> 1` otherwise, is a well-defined homomorphism. It composes with the
natural map `ι: A_Λ -> A_Γ` to the identity. So `ι` is injective and `A_Λ` is a
retract of `A_Γ`. This applies to every odd-saturated `Λ`.

*Proof.* Check the relators of `A_Γ`.

- **Both ends in `Λ`.** A relator of `A_Λ`.
- **Both ends outside `Λ`.** It becomes `1 = 1`.
- **One end `u ∈ Λ`, the other outside, with `m_uv = 2k`.** The relator
  `(uv)^k = (vu)^k` becomes `u^k = u^k`.

`π_Λ ∘ ι` fixes every generator. ∎

*Remark.* The evenness hypothesis cannot be dropped for this map. An odd label
`2k + 1` turns `(uv)^k u = (vu)^k v` into `u^(k+1) = u^k`, forcing `u = 1`. But `u`
has infinite order in `A_Λ`, through `A_Λ -> Z`, `s -> 1`. The retractions
themselves are standard for even Artin groups (they are the ones generalized in
arXiv:2408.12291, per its abstract). The derivation above is self-contained.

**Lemma 5.2 (even-boundary splittings).** Let `V = V_1 ∪ V_2` and `Λ = V_1 ∩ V_2`.
Suppose no edge joins `V_1 \ Λ` to `V_2 \ Λ`, and every edge joining `Λ` to `V \ Λ`
has even label. Then:

- `A_Γ = A_(V_1) *_(A_Λ) A_(V_2)`;
- `A_Λ` is a retract of `A_(V_1)` and of `A_(V_2)`;
- `A_Γ ∈ B_A` iff `A_(V_1), A_(V_2) ∈ B_A`.

*Proof.*

- **Pushout.** The pushout of `A_(V_1) <- A_Λ -> A_(V_2)` has generators `V`. Its
  relators are those of the edges of `Γ[V_1]` and of `Γ[V_2]`. Every edge of `Γ` lies
  in one of the two induced subgraphs, so this is the presentation of `A_Γ`.
- **Injectivity.** Lemma 5.1, applied inside `Γ[V_i]`, shows that `A_Λ -> A_(V_i)` is
  injective with a retraction: the edges from `Λ` to `V_i \ Λ` are among the even
  boundary edges. So the pushout is an honest amalgamated product, and `A_(V_i)`
  embeds in `A_Γ`.
- **`B_A`.** "Only if" is closure under subgroups (I1). "If" is Theorem A. ∎

**Lemma 5.3 (inheritance).** For odd-saturated `S`:

- the odd components of `Γ[S]` are the odd components of `Γ` contained in `S`;
- `Q(Γ[S])` is the induced subgraph of `Q` on them.

*Proof.* The odd edges of `Γ[S]` are the odd edges of `Γ` inside `S`. Every odd
component `O ⊆ S` keeps all its odd edges. Edges between two components inside `S`
lie in `Γ[S]`. ∎

**Proof of Theorem B.**

*Only if.* Every union of odd components is odd-saturated, so its Artin group embeds
in `A_Γ` (Lemma 5.1). Then use (I1).

*If.* Induct on the number `k` of odd components.

- **If `Q` is complete** (including `k ≤ 1`), `S = V` is one of the given unions,
  and there is nothing to prove.
- **Otherwise** pick odd components `O, O'` that are not adjacent in `Q`.
  - Let `Λ` be the union of the odd components adjacent to `O` in `Q`. Put
    `V_1 = V \ O` and `V_2 = O ∪ Λ`.
  - **The splitting.** `V_1 ∩ V_2 = Λ`, since `O ∩ Λ = ∅`. An edge from
    `V_2 \ Λ = O` to `V \ O` has its other end in a component adjacent to `O`, that is
    in `Λ`. So no edge joins `V_1 \ Λ` to `V_2 \ Λ`. `Λ` is odd-saturated, so its
    boundary edges are even. Lemma 5.2 applies.
  - **The induction.** `V_1` and `V_2` are odd-saturated and each has fewer than `k`
    odd components: `O ⊄ V_1` and `O' ⊄ V_2`. By Lemma 5.3, every clique of
    `Q(Γ[V_i])` is a clique of `Q`, so the hypothesis holds for `Γ[V_i]`. By
    induction `A_(V_1), A_(V_2) ∈ B_A`.
  - Lemma 5.2 gives `A_Γ ∈ B_A`. ∎

When `Λ = ∅` the step is a free product, which is Theorem A with `C = 1` (and BFFHZ
Corollary F).

## 6. Corollaries C and D, and examples

**Corollary C (even graphs).** If every label of `Γ` is even, the odd components
are the single vertices and `Q` is the underlying graph of `Γ`. So `A_Γ ∈ B_A` iff
`A_Δ ∈ B_A` for every clique `Δ` of `Γ`. By Lemma 5.1, maximal cliques suffice.

**Clique factors.** Let `Δ` be an even clique, and `D(Δ)` the subgraph of its edges
with label `≥ 4`.

- Two vertices in different components of `D(Δ)` are joined by a label-2 edge. So
  `A_Δ` is the direct product of the Artin groups of the components of `D(Δ)`, read
  off the presentation.
- Each factor is an *irreducible* even Artin group on a complete graph.
- `A_Δ ∈ B_A` iff every factor is, by (I1).

**The factors known to lie in `B_A`.**

- A vertex: `Z`.
- An edge labelled `2k`: the dihedral type `I_2(2k)`, which is spherical
  (`spherical-artin-groups-satisfy-permutational-boone-higman`).
- A path `a -4- b -4- c` with `m_ac = 2`: the Euclidean type `C̃_2`, whose Coxeter
  diagram is exactly this path (`c-tilde-artin-groups-satisfy-permutational-boone-higman`,
  case `n = 2`).

No other irreducible spherical diagram is even: every irreducible spherical diagram on
at least three vertices (`A_n`, `B_n`, `D_n`, `E_6`, `E_7`, `E_8`, `F_4`, `H_3`, `H_4`)
has an edge labelled 3. Among the Euclidean diagrams recorded in the graph as in
`B_A` (`Ã_n`, `C̃_n`, `B̃_n`, `G̃_2`), only `C̃_2` has no label 3.

**Corollary D.** Let `Γ` be even, and suppose every component of every `D(Δ)` is a
vertex, an edge, or a `4-4` path. Then `A_Γ ∈ B_A`. Hence `A_Γ` embeds in a finitely
presented simple group and has solvable word problem (I4).

**Even FC type.** `A_Γ` is of FC type when every clique spans a spherical-type Artin
group. For even `Γ` this means every `D(Δ)` is a matching, by the list above.
Equivalently, every triangle of `Γ` has at least two edges labelled 2. These graphs
satisfy Corollary D, so **every even Artin group of FC type lies in `B_A`.**

**Corollary E (clustered odd components, FC type).** Suppose:

- `A_Γ` is of FC type;
- every odd component spans a clique of `Γ`;
- any two odd components joined by an edge are completely joined.

Then every union of odd components in a clique of `Q` is a clique of `Γ`. So its
Artin group is spherical and lies in `B_A`, and Theorem B gives `A_Γ ∈ B_A`.

**Examples.**

- (E1) **The labelled 4-cycle** `a -4- b -4- c -4- d -4- a`.
  - It is triangle-free and even, so FC. Hence `A ∈ B_A`.
  - Explicitly: `A = A(b -4- a -4- d) *_(<b, d>) A(b -4- c -4- d)`, with
    `<b, d> ≅ F_2` a retract of both factors.
  - Each factor is `I_2(4) *_(Z) I_2(4)` over a retract `Z`. It is not of the form
    `<b, d> × K`.
    - A direct factor is normal.
    - Killing `d` maps `A(b -4- a -4- d)` onto `I_2(4) = A(a -4- b)`, and `<b, d>` onto
      `<b>`.
    - `<b>` is not normal in `I_2(4)`. If `a b a^-1 = b^n`, abelianizing gives `n = 1`.
      But `a` and `b` do not commute: their images in the dihedral group of order 8
      are non-commuting reflections.
    - So Part 1 of `pbh-class-closed-under-graph-products` does not apply to this
      splitting.
  - It is two-dimensional. It is not virtually cocompactly cubulated by
    Huang--Jankiewicz--Przytycki, Theorem 1.1, since its defining graph is connected,
    not a vertex or an edge, and has an interior edge labelled 4.
- (E2) **Every even Artin group with triangle-free defining graph.**
- (E3) **A non-FC example:** the `C̃_2` triangle `a -4- b -4- c`, `m_ac = 2`, with a
  pendant edge `c -6- d`. Its maximal cliques are `{a, b, c}` (`C̃_2`) and `{c, d}`
  (`I_2(6)`).
- (E4) **A mixed-parity example.** Vertices `a, b, c, d, e` with `m_ab = 3`,
  `m_bc = 4`, `m_ac = 2`, `m_cd = 4`, `m_de = 3`, `m_ce = 2`, and no other edges.
  - Odd components: `{a, b}`, `{c}`, `{d, e}`. `Q` is a path.
  - The unions over cliques of `Q` are `{a, b, c}` and `{c, d, e}`, both of type `B_3`.
  - So `A_Γ = A(B_3) *_(<c>) A(B_3) ∈ B_A`. It is Corollary E.

## 7. Where the method stops

- (S1) **Odd separators.** Theorem B does nothing when `Γ` has a single odd
  component, for example the 4-cycle with all labels 3, or any connected graph with
  all labels odd.
  - More is true: odd edges genuinely block retractions. In
    `A_3 = <s, t, u | sts = tst, tut = utu, su = us>` the subgroup `<s, u> ≅ Z^2` is not
    a homomorphic retract. All generators are conjugate, so `A_3^ab = Z`, and every
    homomorphism `A_3 -> Z^2` has cyclic image.
  - The FC-type "retractions to parabolic subgroups" of Cisneros de la Cruz--Cumplido--Foniqi
    (arXiv:2408.12291) therefore cannot all be homomorphisms. The paper was not read
    beyond its abstract. Presumably they are set-theoretic retractions, and as such
    they do not feed Theorem A.
- (S2) **Irreducible even cliques.** Corollary C reduces Boone--Higman (in the form
  `B_A`) for **all** even Artin groups to irreducible even Artin groups on complete
  graphs. Corollary D settles those on at most two vertices and `C̃_2`. Open:
  - every even triangle with at most one label 2 other than `(4,4,2)`, such as
    `(2,4,6)`, `(2,6,6)`, `(4,4,4)`, `(4,4,6)`. All are hyperbolic triangles,
    `1/p + 1/q + 1/r < 1`;
  - all larger irreducible even cliques.

  The triangles are two-dimensional. The Artin node's attempts 3--4 (Jankiewicz
  splittings, decidable-edge HNN extensions) are the relevant lane.
- (S3) **Twisted HNN extensions over retracts.** `<X, t | t c t^-1 = φ(c), c ∈ C>`,
  with `C` a retract of `X` and `φ ∈ Aut(C)`, equals `X *_C (C ⋊_φ Z)`.
  - `C` is a retract of `C ⋊_φ Z` only when `φ` is inner. A retraction sends `t` to
    some `s ∈ C`, and then `φ(c) = s c s^-1`.
  - When `φ` is conjugation by `s`, the letter `s^-1 t` centralizes `C`. The extension
    is then the centralizing one, Part 1 of `pbh-class-closed-under-graph-products`
    with `K = Z`.
  - Theorem A does not reach outer `φ`. A natural attempt is to let `t` act by
    `γ`-type twists realizing `φ`. It needs `φ` to be induced by conjugation inside the
    envelope `H`, which (F) does not give.
- (S4) **One-sided retracts.** If `C` is a retract of `X` only, nothing is claimed.
  BFFHZ (l.682--687 of their extracted text, as quoted in
  `pbh-class-closed-under-graph-products`) explain why general amalgams are excluded:
  the word problem of `X *_C Y` involves membership in `C`.

## 8. Literature check (bounded, 2026-09-16)

**Read at source here (2026-09-16).**

- J. Huang, K. Jankiewicz, P. Przytycki, *Cocompactly cubulated 2-dimensional Artin
  groups*, arXiv:1510.08493v1 (28 Oct 2015). Theorem 1.1, read from the extracted PDF
  text:

  > "Let A be a 2-dimensional Artin group. Then the following are equivalent. (i) A
  > is cocompactly cubulated, (ii) A is virtually cocompactly cubulated, (iii) each
  > connected component of the defining graph of A is either a vertex, or an edge, or
  > else all its interior edges are labeled by 2 and all its leaves are labelled by
  > even numbers."

  The same text notes that tree-defined Artin groups are cubulated through graph
  manifolds.
- T. Haettel, *Virtually cocompactly cubulated Artin-Tits groups*,
  arXiv:1509.08711v5 (13 Apr 2020). Abstract and Corollary G, from the extracted PDF
  text: a spherical-type Artin group is virtually cocompactly cubulated iff every
  irreducible parabolic subgroup has rank at most 2. The classification is proved for
  spherical, FC and two-dimensional types.
- R. Blasco-García, C. Martínez-Pérez, L. Paris, *Poly-freeness of even Artin groups
  of FC type*, arXiv:1705.05574v1 (16 May 2017). Abstract verbatim: "We prove that
  even Artin groups of FC type are poly-free and residually finite." Linearity is not
  mentioned in the abstract.
- B. A. Cisneros de la Cruz, M. Cumplido, I. Foniqi, *On Artin groups admitting
  retractions to parabolic subgroups*, arXiv:2408.12291v1 (22 Aug 2024). Abstract
  only; see (S1).
- A. Juhász, arXiv:2507.16770v1 (22 Jul 2025). Abstract read on an earlier pass of
  this lane: solvable word problem for Artin groups whose defining graph has no edge
  labelled 3, with an `n^6` isoperimetric function. It is not about embeddings.
- arXiv listing search "even Artin groups" (2026-09-16), titles and abstracts only.
  No entry about Boone--Higman, finitely presented simple groups, or linearity of
  even Artin groups.
- arXiv title search `"even Artin"` (2026-09-16), eleven entries, titles and abstract
  summaries only. They are: cohomology rings and p-local behaviour (arXiv:2606.30558);
  second integral homology (arXiv:2507.04577); Tits alternative for subgroups of even
  FC type (Antolín--Foniqi, arXiv:2305.17292); intersections of parabolic subgroups
  (arXiv:2204.14080); homology of even Artin kernels (arXiv:2102.11817); Σ-invariants
  (arXiv:2011.07608, arXiv:2009.14269); poly-freeness of large even Artin groups
  (arXiv:2009.08747); the isomorphism problem (arXiv:1909.00572); quasi-projectivity
  (arXiv:1803.05274); and BMP (arXiv:1705.05574). None is about linearity, virtual
  specialness, or embeddings in simple groups. An arXiv full-text search "even Artin
  linear" returned nothing relevant.

**Through graph nodes (quotes pinned there, not re-read here).**

- BFFHZ arXiv:2503.21882v2: Theorems C and E, Question 3.1, and the list of Artin
  types after Corollary B.
- Zaremsky arXiv:2405.18354: Corollary B and Proposition 5.5.
- Belk--Bleak--Matucci--Zaremsky arXiv:2306.16356v3: Problem 5.3(13) and Remark 5.4.
- Godelle--Paris arXiv:1105.1048, Theorem C, through
  `artin-word-problem-reduces-to-free-of-infinity-graphs`.

**What the search did not find.**

- Any theorem putting even Artin groups of FC type (beyond right-angled, spherical,
  Euclidean, or forest-defined ones) into a finitely presented simple group or into
  `B_A`.
- Any closure of `B_A` or of the Boone--Higman class under amalgams over common
  retracts.

The graph's own nodes on Artin groups, graph products, relative holomorphs,
permutational wreaths and HNN extensions do not contain these statements. Search of
the graph: `bin/cairn search` and a grep of `research/` for "even Artin", "twisted
retract", "common retract" (2026-09-16).

**Bounded, not exhaustive.**

- MathSciNet and Google Scholar were not searched.
- Linearity of even FC-type Artin groups was not settled either way. If they are
  known to be linear in characteristic zero, Corollary D's FC case follows from
  `char-zero-linear-groups-satisfy-permutational-boone-higman`, and only Theorems A
  and B and the non-FC cases stay new. The residual finiteness theorem of 2017,
  proved by poly-freeness, suggests that linearity was not available then.
