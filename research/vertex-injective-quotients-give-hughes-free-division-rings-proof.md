---
rg: 2
id: vertex-injective-quotients-give-hughes-free-division-rings-proof
kind: route
title: The kernel of a vertex-injective map acts freely on the Bass-Serre tree, so Hughes' extension lemma over that free kernel builds the Hughes-free field, and a coinduced wreath product supplies the maps for retract trees
target: vertex-injective-quotients-give-hughes-free-division-rings
requires:
  - hughes-extension-lemma-and-fsp-universal-field-imports
  - fsp-graph-of-rings-and-linnell-extension-imports
  - hughes-free-division-rings-pass-to-directed-unions
---

## Inputs

- **(HE)** Hughes' extension lemma, and the fact that bi-orderable groups are HFE: items 1–2 of
  [[hughes-extension-lemma-and-fsp-universal-field-imports]].
- **(7.6)** FSP Lemma 7.6: item 3 there.
- **(JZ)** `D_{k*G}` exists over every division ring for `G` locally indicable amenable, residually torsion-free
  nilpotent, or free-by-cyclic, and so for free groups. **(R)** Restriction: for `H ≤ G`, the division closure of
  `k*H` in `D_{k*G}` is Hughes-free for `k*H`. These are items 1–2 of
  [[fsp-graph-of-rings-and-linnell-extension-imports]].
- **(DU)** Directed unions: [[hughes-free-division-rings-pass-to-directed-unions]].
- **Bass–Serre theory** (Serre, *Trees*). A group acting on a tree without inversions and with trivial vertex
  stabilizers is free. If `G` is the fundamental group of a graph of groups, its vertex stabilizers on the
  Bass–Serre tree `T` are the conjugates of the vertex groups. The fundamental group of a connected subgraph of
  groups embeds in `G`. An infinite tree of groups is the directed union of the fundamental groups of its finite
  subtrees.

A restriction of a crossed product `E * G` to a subgroup `L` is a crossed product `E * L`. This is used without
comment.

## Item 1: the class `𝓗`

Every member of `𝓗` is HFE and so locally indicable.

- **Subgroups.** Closure under subgroups holds by definition.
- **Extensions.** Let `N ⊴ G` with `N, G/N ∈ 𝓗`. `G` is locally indicable. Indeed, let `H ≤ G` be finitely
  generated and nontrivial. If `H ≤ N`, then `H` maps onto `Z`. Otherwise its image in `G/N` is finitely
  generated and nontrivial, so it maps onto `Z`.

  Let `L ≤ G`. Then `L ∩ N ≤ N` is HFE and `L/(L ∩ N) ≅ LN/N ≤ G/N` is HFE. Both are locally indicable. By
  (HE), every `E * L` has a Hughes-free division ring, because `E * (L ∩ N)` has one. So `L` is HFE, and
  `G ∈ 𝓗`.
- **Directed unions.** Let `G = ∪ G_i` be directed with `G_i ∈ 𝓗`, and let `L ≤ G`. Then `L = ∪ (L ∩ G_i)` is
  directed with HFE members. Given `E * L`, each `E * (L ∩ G_i)` has a Hughes-free division ring, so `E * L` has
  one by (DU). Hence `G ∈ 𝓗`.
- **Members.**
  - Free groups: their subgroups are free, so apply (JZ).
  - Locally indicable amenable groups: closed under subgroups, so apply (JZ).
  - Bi-orderable groups: closed under subgroups, so apply (HE).
  - Residually torsion-free nilpotent groups: closed under subgroups, so apply (JZ).
  - Free-by-cyclic groups: an extension of a free group by `Z`, so in `𝓗` by extension closure.

## Item 2: vertex-injective criterion

**(⇒)** Take `Q = G` and `φ = id`.

**(⇐)** Let `φ: G -> Q`, with `Q ∈ 𝓗`, be injective on each vertex group, and set `F = ker φ`. The stabilizer
in `F` of a vertex `gv` of `T` is `F ∩ g G_v g^{-1} = g (F ∩ G_v) g^{-1}`, since `F` is normal, and this is
trivial. So `F` acts freely on `T`, without inversions, and is free. Hence `F ∈ 𝓗`. Also
`G/F ≅ φ(G) ≤ Q`, so `G/F ∈ 𝓗`, and `G ∈ 𝓗` by item 1.

## Item 3: embedding problems

- **Amalgams.** If `ι_A: A -> Q` and `ι_B: B -> Q` are embeddings into `Q ∈ 𝓗` that agree on `C`, they induce
  `A *_C B -> Q`, which is injective on both vertex groups. Apply item 2. Conversely, take
  `Q = A *_C B`.
- **HNN extensions.** Let `B ≤ Q ∈ 𝓗`, and suppose `q ∈ Q` satisfies `q^{-1} a q = θ(a)` for `a ∈ A`. Then
  `t ↦ q` extends the inclusion to `B *_θ -> Q`, injective on the single vertex group `B`. Apply item 2.
  Conversely, take `Q = B *_θ`.

## Item 4: free products

Let `A, B ∈ 𝓗`. Then `A × B` is an extension of `A` by `B`, so it lies in `𝓗` by item 1. The natural map
`A * B -> A × B` is injective on `A` and on `B`. Apply item 2. (Its kernel is the free Cartesian subgroup
`[A, B]`.)

## Item 5: folds

For `C ≤ B ≤ A` with `A ∈ 𝓗`, the map `A *_C B -> A` is the identity on `A` and the inclusion on `B`. It is
well defined, since both maps restrict to the inclusion on `C`, and it is injective on both vertex groups. Apply
item 2 with `Q = A`. The double is the case `B = A`.

## Item 6: retract trees

**Gluing lemma.** Let `P ∈ 𝓗` and `M ≤ P`. Let `V = K ⋊ M'` with `V ∈ 𝓗`, where `α: M' -> M` is an
isomorphism. Then there is `P' ∈ 𝓗` with `P ≤ P'`, and an embedding `j: V -> P'` with `j|_{M'} = α`.

*Proof.* Identify `M'` with `M` through `α`, and write `m·k` for the action of `M` on `K`. Let `X` be the set of
functions `f: P -> K` satisfying:
- `f(mp) = m·f(p)` for all `m ∈ M` and `p ∈ P`;
- `f` is trivial outside finitely many right cosets `Mp`.

1. **`X` is a group, isomorphic to `⊕_{M\P} K`.** It is a group under pointwise multiplication, because each
   `m·` is an automorphism. Choosing coset representatives identifies it with `⊕_{M\P} K`.
2. **`P` acts on `X`.** Set `(p·f)(x) = f(xp)`. This preserves the equivariance condition, since
   `(p·f)(mx) = f(mxp) = m·f(xp)`. It is a left action, since `(p_1·(p_2·f))(x) = f(x p_1 p_2)`.
3. **`P' ∈ 𝓗`.** Put `P' = X ⋊ P`. Each `K ≤ V` lies in `𝓗`, so every finite direct power of `K` lies in `𝓗`
   by extension closure. Their directed union `X` then lies in `𝓗`. Hence `P' ∈ 𝓗`, again by extension closure.
4. **The map `ι: K -> X`.** For `k ∈ K`, let `f_k(m) = m·k` for `m ∈ M`, and `f_k(x) = 1` for `x ∉ M`. Then
   `f_k ∈ X`, and `ι: k ↦ f_k` is an injective homomorphism.
5. **`ι` is `M`-equivariant.** Let `m_0 ∈ M`. For `x ∈ M`, `(m_0·f_k)(x) = f_k(x m_0) = x·(m_0·k)`. For
   `x ∉ M`, `x m_0 ∉ M`, so the value is `1`. Hence `m_0 ι(k) m_0^{-1} = m_0·ι(k) = ι(m_0·k)`.
6. **The embedding `j`.** So `j(k m) = ι(k) m` is a homomorphism `K ⋊ M -> X ⋊ P`. It is injective because
   `ι` is injective and `X ∩ P = 1`, and it restricts to the inclusion on `M`. □

**Finite trees.** Let `𝒯` be finite and oriented toward a root `r`. We show by induction on the number of
vertices that there is a homomorphism `ψ: π_1(𝒯) -> P` with `P ∈ 𝓗`, injective on every vertex group.
- **One vertex.** Take `ψ = id`, with `P = G_r ∈ 𝓗`.
- **Induction step.** Otherwise pick a leaf `v ≠ r`, with outgoing edge `e` to `u`. Here `G_v = K_v ⋊ G_e` by
  the retraction. Let `ψ': π_1(𝒯 - v) -> P` be given by induction. Since `ψ'` is injective on `G_u ⊇ G_e`, the
  map `α = ψ'|_{G_e}` is an isomorphism onto `M = ψ'(G_e)`. The gluing lemma, with `V = G_v`, gives
  `P' ⊇ P` and `j: G_v -> P'` with `j|_{G_e} = α`. Since `π_1(𝒯) = π_1(𝒯 - v) *_{G_e} G_v`, the maps `ψ'` and
  `j` combine into `ψ: π_1(𝒯) -> P'`. It is injective on every vertex group.

By item 2, `π_1(𝒯) ∈ 𝓗`.

**Infinite trees.** Each finite subtree `𝒮` inherits an orientation with a root:
- the given root, if `𝒮` contains it and the orientation is toward a vertex;
- otherwise, the vertex of `𝒮` closest to the root, or to the end.

Every non-root vertex of `𝒮` has its outgoing edge inside `𝒮`. So `π_1(𝒮) ∈ 𝓗`. `π_1(𝒯)` is the directed union
of these subgroups, so `π_1(𝒯) ∈ 𝓗` by item 1.

**HNN extensions.** Let `G = B *_θ`, with `t^{-1} a t = θ(a)` for `a ∈ A`. Let `G -> Z` send `t ↦ 1` and
`B ↦ 0`, and let `N` be its kernel. Then `N` is the fundamental group of a line of groups:
- its vertex groups are `B_i = t^i B t^{-i}`, for `i ∈ Z`;
- `B_i ∩ B_{i+1}` is the edge group `t^i A t^{-i} = t^{i+1} C t^{-(i+1)}`.

So in `B_i`, the edge toward `i+1` is the conjugate of `A`, and the edge toward `i-1` is the conjugate of `C`.
- If `B` retracts onto `A`, orient the line toward `+∞`.
- If `B` retracts onto `C`, orient it toward `-∞`.

In either case every vertex retracts onto its outgoing edge, so `N ∈ 𝓗`. Then `G ∈ 𝓗` by extension closure,
since `G/N ≅ Z`.

## Item 7: q:HF and compatibility

Let `G ∈ 𝓗` split as `(G_v, G_e; Γ)`. Then `D_{k*G}` exists. By (7.6), `U(DG_Γ) ≅ D_{k*G}` as `k*G`-rings, so
FSP's embedding is Hughes-free. This holds for every splitting.

Now let `N ≤ G`. By (R), the division closure of `k*N` in `U(DG_Γ) ≅ D_{k*G}` is `D_{k*N}`. Let `N` act on any
`N`-invariant subtree of the Bass–Serre tree, for example `T_H` for `N ⊴ H ≤ G`. This gives a splitting of `N`
as a graph of groups whose vertex groups are subgroups of conjugates of the `G_v`. Since `N ∈ 𝓗`, (7.6) applies
to `N` with that splitting and gives `U(DN) ≅ D_{k*N}`. Hence the division closure of `k*N` in `U(DG_Γ)` is
`k*N`-isomorphic to the universal field of `N`'s induced graph of rings. □

## Remark: where the method stops

Item 2 is an equivalence, so membership of a graph of groups in `𝓗` is exactly the existence of a
vertex-injective map to `𝓗`. It is not a theorem that such maps exist for all locally indicable graphs of `𝓗`
groups. In the one-relator setting, the Magnus–Moldavanskii line of a group of primitivity rank 2 has
Magnus-subgroup edges, and the retract condition of item 6 need not hold. The remaining one-relator case is
therefore the HNN embedding problem of item 3, for Magnus shifts `θ` that are not induced by a retraction.
