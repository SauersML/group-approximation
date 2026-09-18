---
rg: 2
id: bbmz-host-finiteness-reduces-to-the-vertex-boundary-groupoid
kind: claim
title: For G*Z on its horofunction boundary, every element is finitary off finitely many coset pieces and groupoid homology in degrees >= 2 is that of G on its own horofunction boundary; so if the simple derived BBMZ host has type F_n, then H_k(G; C(∂_h G, Q)) is finite-dimensional for 2 <= k <= n
requires:
  - li-derived-full-group-homology-is-k-theory-cover
  - li-ah-exact-sequence-for-minimal-comparison-groupoids
  - matui-purely-infinite-minimal-full-groups-have-simple-d
distinct_from:
  twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family: that reduces F_n of the envelope SV_Γ to F_n of the full RSG family; this says what F_n of the full group itself forces, and shows that the free factor Z carries none of the difficulty.
  free-product-boundary-groupoids-carry-the-vertex-group-homology: that compactifies the Bass–Serre tree by collapsing each vertex to a point, and finds H_n(B; Z); here each vertex is blown up into a copy of the vertex group's horofunction boundary, and the higher homology is that of G acting on ∂_h G.
  hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups: that is Zaremsky's open question; this gives a necessary condition, intrinsic to G, for the BBMZ host to answer its F_∞ half.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-18; not reviewed; no priority claimed).
- Items 1–3 are elementary, given the cited facts from BBMZ (arXiv:2309.06224, §4) and BBM.
- Item 4 imports X. Li, arXiv:2209.08087 (Theorem 4.18 and Corollary 5.20), and the
  Cartan–Serre / Milnor–Moore description of the rational homology of H-spaces.
- A bounded search (2 web searches, 09-18) found no F_∞ result for full contracting RSGs beyond
  the bounded case. That case is Belk–Hyde–Matucci, arXiv:2407.03149, Remark `thm:RSGs`: "any
  full, bounded, contracting RSG has type F_∞".

## Setting

- **The groups.** `G` is a nontrivial group with finite generating set `S`, and
  `H = G * <t>` carries the generating set `S ∪ {t}`.
- **The boundary and the host.** `∂_h H` is the horofunction boundary. BBMZ,
  `thrm:FreeProductBoundary`, shows it is a Cantor set on which `H` acts faithfully.
  `Γ_h = [[H | ∂_h H]]` is the BBMZ host.
- **The groupoid.** `𝒢 = H ⋉ ∂_h H`.
- **The tree.** `T` is the Bass–Serre tree of `H` as an HNN extension of `G` over the trivial
  group. Its vertices are the cosets `xG` and its base vertex is `v_0 = G`. Its edges carry
  trivial stabilizers.
- **Cones.** For `w` ending in `t^ε`, `C(w)` is the cone of BBMZ, `lem:ConesAreAtoms`. It is an
  atom, and `w'w^{-1}` is a morphism `C(w) → C(w')` whenever `w'` also ends in `t^ε` (for
  `ε = −1`, see the first line of the proof of `lem:atoms_in_atoms`). `∂C(w)` denotes its shadow.
- **Pieces.** `Y ⊆ ∂_h H` is the set of limits of `d_x` with `x ∈ G`, and `Y_{xG} = xY`.

## Theorem

1. **Decomposition.**
   - `∂_h H = Y ⊔ ⨆_{g∈G, ε=±1} ∂C(g t^ε)`, where `Y` is closed and the shadows are disjoint
     clopen sets.
   - Restriction to `G` is a `G`-equivariant homeomorphism `Y ≅ ∂_h G` (the boundary for `S`).
   - Translating by `x`, the pieces `Y_v` (`v` a vertex of `T`) are pairwise disjoint.
   - Every point of `∂_h H` lies in exactly one piece, or else in a nested infinite sequence of
     cone shadows (the *free part*, which is the space of ends of `T`).
2. **Dynamical inertness.** Let `h ∈ H`. Then `h` maps `C(w)` onto `C(hw)` by a morphism of atoms,
   for every cone `C(w)` except the at most `d_T(v_0, h^{-1}v_0)` cones whose Bass–Serre edges lie
   on the geodesic `[v_0, h^{-1}v_0]`. So each element of `Γ_h`, near every point outside finitely
   many pieces `Y_v`, acts by a morphism of atoms. In addresses, that is a canonical similarity
   followed by an automorphism of a type-subtree drawn from a finite groupoid: a finitary,
   synchronous map.
3. **Homology transfer.**
   - `𝒢` is effective, so `Γ_h = F(𝒢)`.
   - For every abelian group `A` and every `k ≥ 2`,
     `H_k(𝒢; A) ≅ H_k(G ⋉ ∂_h G; A) = H_k(G; C(∂_h G, A))`.
   - `H_1(G; C(∂_h H, A)) → H_1(G; C(∂_h G, A))` is injective.
4. **Rational obstruction.** Suppose `G` is hyperbolic. Then:
   - `𝒢` is minimal and purely infinite, and `D(Γ_h)` is simple;
   - `H_*(D(Γ_h); Q)` is the free graded-commutative algebra on `⊕_{k≥2} H_k(G; C(∂_h G, Q))`,
     with the degree-`k` summand placed in degree `k`;
   - in particular, if `D(Γ_h)` has type FP_n over Q (for instance type F_n), then
     `dim_Q H_k(G; C(∂_h G, Q)) < ∞` for `2 ≤ k ≤ n`;
   - if `Γ_h / D(Γ_h)` is finite, the same holds with `Γ_h` in place of `D(Γ_h)`. In that case,
     since BBMZ prove `Γ_h` finitely presented, `dim_Q H_2(G; C(∂_h G, Q)) < ∞`.
5. **Checks.**
   - **Free groups on a basis.** The condition is empty, since `H_k(G; ·) = 0` for `k ≥ 2`.
   - **Closed orientable hyperbolic n-manifold groups, top degree.** Here
     `H_n(G; C(∂_h G, Q)) ≅ C(∂_h G, Q)^G`, of dimension at most the minimal fibre size of the
     finite-to-one map `∂_h G → ∂G` (Webster–Winchester). For surface groups this is the whole
     condition, and it holds.
   - **The same groups, degrees `2 ≤ k ≤ n−1`.** The condition is that
     `H^{n−k}(G; C(∂_h G, Q)) ≅ Ȟ^{n−k}(E_h; Q)` is finite-dimensional. Here
     `E_h = M̃ ×_G ∂_h G` is the horofunction suspension, a compact space mapping finite-to-one
     onto the unit tangent bundle. This is **OPEN**.

## Proofs

**1.** Write `x ∈ H ∖ G` in normal form as `x = g t^{ε} u`. Then `x ∈ C(gt^ε)`, so `H` is `G`
together with the disjoint cones `C(gt^ε)`.
- Take a horofunction `η = lim d_{x_n}` with `|x_n| → ∞`.
  - If infinitely many `x_n` lie in one cone `C(gt^ε)`, then `η ∈ ∂C(gt^ε)`.
  - Otherwise, pass to `x_n ∈ G`, or to `x_n ∈ C(g_n t^{ε_n})` with `|g_n| → ∞`.
- The edge `g_n — g_n t^{ε_n}` is a bridge of the Cayley graph, which is a tree of copies of
  `Cay(G, S)` joined by `t`-edges. So `d(x_n, z) = d(x_n, g_n) + d(g_n, z)` for every `z` outside
  the cone. Hence `d_{x_n} ≡ d_{g_n}` modulo constants on `B_k` once `|g_n| > k + 1`, and `η ∈ Y`.
- **Disjointness.** A point of `∂C(gt^ε)` is closer to `gt^ε` than to `g`. Every limit of
  `d_x` with `x ∈ G` has the opposite inequality.
- **`Y ≅ ∂_h G`.**
  - `d_H|_G = d_G`, because geodesics between points of `G` stay in the `G`-copy.
  - A horofunction in `Y` is determined by its restriction to `G`: `η(z) = η(g) + d(g, z)` for
    `z ∈ C(gt^ε)`, by the bridge formula.
  - Every `G`-horofunction arises this way.
  - So restriction is a continuous bijection from the compact set `Y` onto `∂_h G`. It is
    `G`-equivariant.
- The remaining statements follow by translating to each vertex of `T`.

**2.** Take `w` ending in `t^ε` and put `e_w` for its edge. The equality `hC(w) = C(hw)` holds
if and only if `hw` ends in `t^ε`.
- That holds if and only if the half-tree beyond `h·e_w` does not contain `v_0`, that is, if the
  half-tree beyond `e_w` does not contain `h^{-1}v_0`.
- Among the edges pointing away from `v_0`, this fails exactly on the geodesic `[v_0, h^{-1}v_0]`.
- For every other cone, `h = (hw)w^{-1}` is a morphism, by `lem:ConesAreAtoms`.
- The points outside all good cones lie on no good half-tree, so they lie in the pieces `Y_v`
  for `v ∈ [v_0, h^{-1}v_0]`.
- By BBMZ property (ii) of a system of addresses, a morphism between atoms of equal type is the
  canonical similarity composed with one of the finitely many self-morphisms of the atom. By
  condition (iii) of `def:morphisms`, a self-morphism maps descendant atoms to descendant atoms,
  so it acts on addresses by a level-preserving tree automorphism.
- Elements of `Γ_h` are piecewise in `H` on a finite clopen partition, so the bad pieces are
  again finite in number.

**3.**
- **Effectiveness.** Suppose `h ≠ 1` fixes a nonempty open set pointwise.
  - By `lem:atoms_in_atoms`, every cone contains a cone `C(w)` with `w` ending in `t`.
  - So `h` fixes pointwise `∂C(w)`, which contains the pieces `Y_v` for all vertices `v` of a
    half-tree.
  - Since `hY_v = Y_{hv}` and the pieces are disjoint, `h` fixes two adjacent vertices, hence an
    edge. Edge stabilizers are trivial, so `h = 1`, a contradiction.
  - So the transformation groupoid is its own groupoid of germs, and `Γ_h = F(𝒢)`.
- **The module sequence.** By item 1 there is an exact sequence of `G`-modules
  `0 → ⊕_{g,ε} C(∂C(gt^ε), A) → C(∂_h H, A) → C(Y, A) → 0`.
  - **Exactness.** A locally constant function that vanishes on `Y` is supported on a compact
    set, which is covered by finitely many shadows. Restriction to a closed subset of a Stone
    space is onto.
  - **The kernel is induced.** `G` permutes the shadows freely, since `g'·C(gt^ε) = C(g'gt^ε)`.
    So the kernel is `Z[G] ⊗ (C(∂C(t), A) ⊕ C(∂C(t^{-1}), A))`, and its homology vanishes in
    degrees `≥ 1` by Shapiro.
  - This gives `H_k(G; C(∂_h H, A)) ≅ H_k(G; C(Y, A))` for `k ≥ 2`, and injectivity for
    `k = 1`.
- **Mayer–Vietoris.** For `H = G * <t>` and any `H`-module `M`,
  `H_k(H; M) ≅ H_k(G; M) ⊕ H_k(Z; M) = H_k(G; M)` when `k ≥ 2`. The terms `H_k(1; M)` and
  `H_{k−1}(1; M)` vanish there.
- Finally, `H_*(Γ ⋉ X; A) = H_*(Γ; C_c(X, A))` (Li, §2.3.2). Combined with `Y ≅ ∂_h G`, this
  proves item 3.

**4.**
- **Minimality.** For hyperbolic `G`, `H` has finitely many atom types, and its type graph has
  an irreducible core (BBMZ `thrm:FreeProductBoundary`). So `V_{Γ,E} ≤ Γ_h`. Every cone
  contains subcones of every core type, so canonical similarities move any point into any cone.
- **Pure infiniteness.** For compact open `U` and nonempty `V`, map the cones of `U`, of core
  type, by canonical similarities into disjoint subcones of `V`.
- **Simplicity.** Purely infinite minimal groupoids have comparison
  (`li-ah-exact-sequence-for-minimal-comparison-groupoids`), and `D(Γ_h)` is simple
  (`matui-purely-infinite-minimal-full-groups-have-simple-d`).
- **Li's theorem.** Corollary 5.20 gives `H_*(D(Γ_h); Q) ≅ H_*(Ω̃^∞_0 K(B_𝒢); Q)`.
  - Theorem 4.18 gives `H_*(K(B_𝒢); Q) ≅ H_*(𝒢; Q)`.
  - `K` is connective, so rationally `π_* K ⊗ Q ≅ H_*(K; Q)`.
  - The universal cover `Ω̃^∞_0 K` is a simply connected infinite loop space, and
    `π_k = π_k K` for `k ≥ 2`.
  - Its rational homology is the free graded-commutative algebra on `π_* ⊗ Q` (Cartan–Serre,
    Milnor–Moore), and `π_k ⊗ Q` sits inside it as the primitives of degree `k`.
  - Item 3 then identifies `π_k ⊗ Q` with `H_k(G; C(∂_h G, Q))` for `k ≥ 2`.
- **The finite-index case.** If `Γ_h / D(Γ_h)` is finite, `Γ_h` and `D(Γ_h)` have the same
  finiteness properties.

**5.**
- **Top degree.** Poincaré duality gives `H_n(G; M) ≅ M^G` for `M = C(∂_h G, Q)`.
  - Every level set of an invariant locally constant function is a nonempty invariant clopen
    set, so it contains a minimal component.
  - Each minimal component maps onto `∂G`, by minimality there, so it meets every fibre.
  - Hence there are at most `m` pairwise disjoint invariant clopen sets, where `m` is the minimal
    fibre size, and `dim M^G ≤ m`.
- **Middle degrees.** The suspension `E_h → M` has totally disconnected fibres and aspherical
  base, so `Ȟ^j(E_h; Q) ≅ H^j(G; C(∂_h G, Q))` by the Leray spectral sequence (standard).

## Why the finite germ extension theorem does not apply (two resolutions of the parabolic vertex)

These are lane observations, with proofs.

**(a) The horofunction resolution chops the singular loci.** Take an atom `A` with
`∂A ∩ Y ≠ ∅` and `Y ⊄ ∂A`.
- By `lem:atoms_in_atoms`, `C(t)` has a descendant `A'` of the same type as `A`.
- The element of `V_{Γ,E}` that swaps `∂A` and `∂A'` by canonical similarities moves
  `∂A ∩ Y` into `∂C(t)`, which misses `Y`. It keeps `Y ∖ ∂A` in `Y`.
- So the pieces are not blocks for `Γ_h`.

The germ complex of Belk–Hyde–Matucci (arXiv:2407.03149, `thm:SingFixFiniteness`) needs
singular loci that the whole group permutes. Item 2 makes each element singular on only finitely
many pieces, but those pieces cannot serve as the singular locations.

**(b) The point resolution has an infinitely generated base.** Collapse every piece `Y_v` to a
point. The quotient is the Bass–Serre tree compactified by its vertices, and its full group
consists of the elements of `Γ_h` that act by a single element of `H` near each whole piece. This
is the analogue, for `G * Z` and its tree with `G`-vertices only, of the stabilizer engine of
`free-product-boundary-groupoids-carry-the-vertex-group-homology` (there `Z/k * B`).
- **What the collapse gains.** The singular loci are now points, and the germ group at a vertex
  is `G` itself, which is F_∞ when `G` is hyperbolic.
- **What it loses.** Consider the base `B^0` of elements whose germ at every vertex point is a
  pure transport in reduced-word coordinates.
  - `B^0` depends only on the pointed set `(G, 1)`.
  - It is **not finitely generated**. Let `σ_{λμ}` exchange two branch letters `λ, μ ∈ G × {±}`
    of the same sign, everywhere in coordinates. Each element of `B^0` commutes with `σ_{λμ}`
    for all `λ, μ` outside the finite set of letters in its partition data. The half-tree
    transpositions `τ_{λν} ∈ B^0` satisfy `σ_{λμ}τ_{λν}σ_{λμ}^{-1} = τ_{μν}`, so no finitely
    generated subgroup contains them all.
  - So hypothesis (1) of that theorem (a base of type F_n) already fails at `n = 1`. Every letter
    change must come from the vertex group, which is how the engine consumes `G`'s word problem
    (`fp-stabilizer-engines-need-decidable-vertex-groups`).

## Lesson for general BH

- **The free factor is inert.** Attaching `Z` to tame the boundary changes neither the
  dynamics nor the higher homology. Every element is finitary off finitely many coset pieces, and
  the homology in degrees `≥ 2` is that of `G` on its own horofunction boundary. So the F_∞ half
  of Zaremsky's question, through the BBMZ host, is a statement about `G ⋉ ∂_h G` alone.
- **Li plus Milnor–Moore give a cheap necessary test.** They turn "the simple derived full group
  is F_n" into finite-dimensional groupoid homology in degrees `2..n`. The test is computable from
  the input action, and it should be run before any Brown's-criterion attempt on a full-group host.
- **The parabolic vertex has two resolutions, and each breaks one hypothesis of the finite germ
  theorem.**
  - The point resolution has atomic singular loci and the input as germ group, but its transport
    base is infinitely generated.
  - The horofunction resolution has a finite-type base, but its singular loci get chopped.
  - An F_∞ proof needs a resolution in between, or a germ theorem for non-atomic singular loci.
    That is the same infinite-emitter gate as SYNTHESIS (IE), now with the input hyperbolic.

## Next

- **Compute the test for one Kazhdan example.** Take a torsion-free cocompact lattice in
  `Sp(n,1)`, which is PD(4n), and compute `Ȟ^j(E_h; Q)` for `1 ≤ j ≤ 4n − 2`.
  - If it is infinite-dimensional in some degree, then `D(Γ_h)` is not F_{4n−j}. When
    `Γ_h / D(Γ_h)` is finite, the full contracting RSG `Γ_h` itself is not F_∞, which answers
    BBMZ Question 1.2 in the negative.
  - If it is finite in every degree, the obstruction is void, and the missing piece is a germ
    theorem for non-atomic singular loci.
- **Prove the top-degree bound for every duality group.** The proof above uses Poincaré
  duality; for a duality group, `H_n(G; M) ≅ Hom_G(H^n(G; ZG), M)`.
