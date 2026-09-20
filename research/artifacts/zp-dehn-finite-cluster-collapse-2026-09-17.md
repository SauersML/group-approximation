# Zaremsky 1.17: collapsing finite clusters of infinite-stabilizer cells

Lane swarm-0917-w21-w21-z-last1, 2026-09-17. It feeds
`finite-infinite-stabilizer-clusters-give-dehn-bound`,
`bs1n-actions-satisfy-the-dehn-action-bound` and the open hole
`some-action-violates-dehn-bound-without-finite-index-faces`.

## 0. Conventions

- Setting (S) is that of `zaremsky-1-17-dehn-function-from-cocompact-action-data`.
- `≼`, `dist^G_H`, admissible maps and `δ_X` are as in Llosa Isenrich–Weis,
  arXiv:2608.07191v1, §2.1 and Definitions 2.2–2.3.
- Normalization (N), as in `sol-lattice-actions-satisfy-the-dehn-action-bound`:
  every Dehn function `δ` is replaced by `max{δ(n), n}`, and `dist_X(n)` by
  `max{dist_X(n), n}`.
- "Without inversions" for a simplicial action means: an element that
  preserves a simplex fixes it pointwise. Stabilizers are the pointwise
  stabilizers `G_σ`, and `σ ⊂ τ` implies `G_τ ≤ G_σ`.
- Each stabilizer `G_σ` carries its own finite generating set. For a finite
  `G_σ` we take all of its elements, so that `ℓ_{G_σ} ≤ 1` on `G_σ`.
- **`X_∞`** is the union of the closed cells of `X` with infinite stabilizer.
  Since `σ ⊂ τ` gives `G_τ ≤ G_σ`, `X_∞` is a `G`-invariant subcomplex. For a
  connected component `C` of `X_∞`, `G_C` is its setwise stabilizer.

## 1. Basic facts about components

**Lemma 1.** Let `C` be a component of `X_∞`.

- (a) If `x` is a vertex of `C`, then `G_x ≤ G_C`.
- (b) If two cells of `C` lie in one `G`-orbit, they lie in one `G_C`-orbit.
  Hence `C / G_C` is finite.
- (c) Every edge of `C` has infinite stabilizer. The 1-skeleton of `C` is
  connected.
- (d) There are finitely many `G`-orbits of components.

*Proof.*

- (a) If `g ∈ G_x`, then `gC` is a component of `X_∞` containing `gx = x`,
  so `gC = C`.
- (b) If `c' = gc` with `c, c' ∈ C`, then `gC` meets `C` in `c'`, so `gC = C`
  and `g ∈ G_C`. `X` has finitely many `G`-orbits of cells.
- (c) An edge of `C` lies in a closed cell `σ` with `G_σ` infinite, and its
  stabilizer contains `G_σ`. A connected simplicial complex has a connected
  1-skeleton.
- (d) Every component contains a cell, and there are finitely many orbits of
  cells. ∎

## 2. The collapse theorem

**Theorem A.** Let `G` act on `X` as in (S), and assume that every connected
component of `X_∞` is finite. Then there is `K ≥ 1` with

```text
δ_G(n) ≼ δ_X(n) · max_x δ_{G_x}( K · δ_X(n) ),            (A)
```

under (N), where `x` ranges over the vertices of `X`. A vertex with finite
stabilizer contributes `m ↦ m`, which every normalized `δ_{G_x}` dominates, so
only infinite stabilizers matter when there are any.

The proof has four steps.

### 2.1 Step 1: subdivide

Let `X'` be the barycentric subdivision of `X`. Its vertices are barycenters
`b_σ`, and its simplices are chains `b_{σ_0}, …, b_{σ_k}` with
`σ_0 < … < σ_k`. Such a simplex has stabilizer `G_{σ_k}`. So `X'_∞ = sd(X_∞)`,
the components of `X'_∞` are the subdivisions of the components of `X_∞`, and
they are finite.

**Lemma 2.** No simplex of `X'` has vertices in two different components of
`X'_∞`.

*Proof.* Let two vertices `b_ρ, b_τ` of one simplex lie in `X'_∞`, with
`ρ < τ`. Then `G_τ` is infinite, the edge `[b_ρ, b_τ]` has stabilizer `G_τ`,
so it lies in `X'_∞`, and the two vertices lie in one component. ∎

`X'` is simply connected. The action on it is cellular, cocompact and without
inversions. Vertex dimension is a `G`-invariant label, and adjacent vertices
have different labels.

**Lemma 3.** `δ_{X'}(n) ≤ 6 δ_X(n) + c_0 n` for a constant `c_0`.

*Proof.*

- Choose a vertex `v(σ)` of each cell `σ`, equivariantly. Pick one per orbit
  representative and transport it. This is well defined because `G_σ` fixes
  `σ` pointwise.
- An edge loop of length `n` in `X'` maps under `b_σ ↦ v(σ)` to an edge path
  of length at most `n` in `X^(1)`. Adjacent `b_ρ, b_σ` with `ρ < σ` go to
  vertices of `σ`, which are equal or adjacent.
- Each `X'`-edge and its image are homotopic rel endpoints inside the closed
  star of one simplex of `X`, through at most `c_0` triangles of `X'`.
- A filling of the image of area `A` subdivides to a filling in `X'` of area
  `6A`. ∎

### 2.2 Step 2: collapse each cluster to a cone vertex

Let `𝒞` be the set of components of `X'_∞`. Each is finite. By Lemma 1(d) applied to `X'`
(whose proof uses only cocompactness and no inversions), there are finitely many `G`-orbits of them. Set
`D = max_{C ∈ 𝒞} diam_{C^(1)}(C^(0))`. This is finite: `C^(1)` is connected by
Lemma 1(c), and `D` only needs one `C` per orbit.

Define a map on vertices
`f : X'^(0) → Y^(0) = (X'^(0) \ X'_∞) ⊔ { c_C : C ∈ 𝒞 }` by `f(v) = c_C` for
`v ∈ C`, and `f(v) = v` otherwise. Let `Y` be the abstract simplicial complex
whose simplices are the sets `f(τ)`, for `τ` a simplex of `X'`. A face of
`f(τ)` is `f` of a face of `τ`, so `Y` is a simplicial complex. `f` is a
simplicial map `X' → Y`. `G` acts on `Y` by `g c_C = c_{gC}`, and `f` is
`G`-equivariant.

- **Cone vertices.** By Lemma 2, every simplex of `Y` contains at most one cone
  vertex `c_C`.
- **Cocompact.** `f` is onto on simplices, so `Y` has finitely many `G`-orbits
  of simplices.

### 2.3 Step 3: `Y` is simply connected, and `δ_Y(n) ≤ δ_{X'}((D + 1) n)`

Let `y_0, y_1, …, y_n = y_0` be an edge loop in `Y`. Each edge
`[y_{i-1}, y_i]` equals `f(ε_i)` for an edge `ε_i = [a_i, b_i]` of `X'`, with
`f(a_i) = y_{i-1}` and `f(b_i) = y_i`. At each `y_i`, join `b_i` to `a_{i+1}`
(indices mod `n`):

- if `y_i` is not a cone vertex, then `b_i = a_{i+1} = y_i`;
- if `y_i = c_C`, then `b_i, a_{i+1} ∈ C`, and we join them by an edge path in
  `C^(1)` of length at most `D`.

This gives an edge loop `γ'` in `X'` of length at most `(D + 1) n`. Its image
`f ∘ γ'` is the loop `y_0 … y_n`, with constant stretches at the cone vertices
where `γ'` runs inside some `C`. Take an admissible filling `Δ → X'` of `γ'`
with `FVol ≤ δ_{X'}((D + 1) n)`, and compose it with `f`:

- a 2-cell of `Δ` sent onto a triangle of `X'` goes either onto a triangle of
  `Y`, or into the 1-skeleton if `f` degenerates that triangle;
- the rest of `Δ` already goes to the 1-skeleton.

So `f ∘ Δ` is an admissible filling of the given loop, up to reparametrizing
the constant stretches, with no larger `FVol`. Every loop in `|Y|` is
homotopic to an edge loop, so `Y` is simply connected, and

```text
δ_Y(n) ≤ δ_{X'}((D + 1) n) ≤ 6 δ_X((D + 1) n) + c_0 (D + 1) n.
```

### 2.4 Step 4: stabilizers of `Y`, and Theorem C

Lemma 1 applies to `X'`. Its proof uses only cocompactness and the absence of
inversions, and both hold for `X'` by Step 1.

- **(i) Vertices.** `Stab_G(c_C) = G_C`. A non-cone vertex `v` of `Y` lies
  outside `X'_∞`, so `Stab_G(v) = G_v` is finite. (`g` fixes `v` in `Y` iff it
  fixes `v` in `X'`, because `f` is the identity off `X'_∞` and cone vertices
  are not identified with other vertices.)
- **(ii) Edges.** Every simplex of `Y` of dimension `≥ 1` contains a non-cone
  vertex, by the one-cone-vertex property. So its pointwise stabilizer is
  finite. In particular every edge stabilizer `G_e` is finite, hence finitely
  generated, and `[G_e : G_σ] ≤ |G_e| < ∞` for every 2-simplex `σ ⊃ e`.
- **(iii) No inversions.** Label `c_C` by `∞` and a non-cone vertex `b_σ` by
  `dim σ`. `G` preserves labels. The vertices of a simplex `f(τ)` carry
  distinct labels: the non-cone ones are distinct vertices of the chain `τ`,
  and there is at most one cone vertex. So an element preserving a simplex
  fixes it pointwise.
- **(iv) Cone stabilizers.** Let `C ∈ 𝒞`. `C` contains a vertex `x` of `X`:
  if `b_σ ∈ C` and `v` is a vertex of `σ`, then `[b_v, b_σ]` has stabilizer
  `G_σ`, which is infinite, so `b_v ∈ C`. `G_C` permutes the finite set
  `C^(0)`, and the kernel of this action lies in `G_x`. So
  `[G_C : G_x] < ∞`. `G_x` is finitely presented by (S), so `G_C` is finitely
  presented. `G_x ↪ G_C` is a quasi-isometry, and the Dehn function is a
  quasi-isometry invariant of finitely presented groups (Alonso, *Inégalités
  isopérimétriques et quasi-isométries*, C. R. Acad. Sci. Paris 311 (1990)).
  So `δ_{G_C} ≃ δ_{G_x}`. Conversely every vertex `x` of `X` with `G_x`
  infinite lies in some `C`.

So `G ↷ Y` satisfies every hypothesis of Theorem C
(`llosa-isenrich-weis-dehn-bound-for-cocompact-actions`): cellular,
cocompact, without inversion, `Y` simply connected and simplicial, vertex
stabilizers finitely presented, edge stabilizers finitely generated, and
`[G_e : G_σ] < ∞`.

**Reading of Theorem C.** We use Theorem C under (N), exactly as the root
statement (UB) is read in `sol-lattice-actions-satisfy-the-dehn-action-bound`.
Read literally, Theorem C gives `δ_{ℤ²} ≼ 0` for the free action of `ℤ²` on
the plane. So the imported statement is only meaningful under a normalization
of this kind. §3.1 of arXiv:2608.07191 estimates areas by
`max_v δ_{G_v}(n + edist_X(Dn))`, which (N) encodes (see
`research/artifacts/sol-lattice-dehn-action-bound-2026-09-16.md`, §0).

**Computing the right-hand side for `Y`.**

- Each `G_e` is finite with all of its elements as generators. So
  `dist^G_{G_e}(m) ≤ 1`, and under (N) `edist_Y(m) = m`. Its superadditive
  closure is `m ↦ m`.
- A finite vertex group has normalized Dehn function `≤ c_F m` for a constant
  `c_F`, which is `≤ c_F δ_{G_x}(m)` for any `x`.
- There are finitely many orbits of vertices, and conjugate stabilizers have
  the same Dehn function.

Theorem C for `Y` gives

```text
δ_G(n) ≼ δ_Y(n) · max_{C} δ_{G_C}( δ_Y(n) )
       ≼ δ_Y(n) · max_{x : G_x infinite} δ_{G_x}( C_1 δ_Y(n) + C_1 )
```

by (iv). If no `G_x` is infinite, the maximum is read as `m ↦ m`. Under (N)
and for `n ≥ 1`, Step 3 gives
`C_1 δ_Y(n) + C_1 ≤ K δ_X((D + 1) n)` and `δ_Y(n) ≤ K δ_X((D + 1) n)` for a
constant `K`. Write `g(n) = δ_X(n) · max_x δ_{G_x}(K δ_X(n))`. This is
nondecreasing, and the right-hand side is `≤ K g((D + 1) n)`. Composing with
`≼` absorbs `(D + 1) n` into the outer argument, which gives (A). ∎

## 3. From (A) to (UB)

(A) differs from (UB) only by the constant `K` inside the argument of
`δ_{G_x}`. Under (N), `dist_X‾(m) ≥ dist_X(m) ≥ m`.

**Corollary 3.1 (doubling vertex groups).** If each `δ_{G_x}` with `G_x`
infinite satisfies `δ_{G_x}(K m) ≤ C_K δ_{G_x}(m)` (for example, if it is
`≃` to a polynomial), then (UB) holds literally for every finite generating
set of `G`.

*Proof.* `δ_{G_x}(K δ_X(n)) ≤ C_K δ_{G_x}(δ_X(n)) ≤ C_K δ_{G_x}(dist_X‾(δ_X(n)))`. ∎

**Corollary 3.2 (no hypothesis on vertex groups).** Fix a finite generating
set `S` of `G`. There is `R` such that (UB) holds, with `dist_X` computed from
the word length of `S_R = { g : ℓ_S(g) ≤ R }`.

*Proof.* If no `G_x` is infinite, then (A) reads `δ_G ≼ δ_X(n)²`, which is at
most the right-hand side of (UB) under (N). Otherwise:

- Let `H = G_x` be infinite, and let `c = max ℓ_S` over the generators of `H`.
  An `H`-geodesic ray from `1` has `ℓ_S` changing by at most `c` per step and
  unbounded. So for each `m ≥ c` it passes through some `h` with
  `m − c ≤ ℓ_S(h) ≤ m`, and `ℓ_H(h) ≥ ℓ_S(h) / c`. Hence
  `dist^S_H(m) ≥ m/c − 2`.
- If `ℓ_S(h) ≤ R m`, then `ℓ_{S_R}(h) ≤ m`. So
  `dist^{S_R}_H(m) ≥ dist^S_H(R m) ≥ R m / c − 2`.
- Take `R = c (K + 2)`. For `m ≥ 1`, `dist^{S_R}_X(m) ≥ (K + 2) m − 2 ≥ K m`.

So `dist^{S_R}_X‾(δ_X(n)) ≥ K δ_X(n)`, and the right-hand side of (A) is at
most that of (UB) for `S_R`. `δ_G` does not depend on `S` up to `≃`. ∎

`δ_G`, `δ_X` and the `δ_{G_v}` are invariants up to `≃`, but `dist_X` depends
on the generating set of `G` through an inner constant. So Corollary 3.2 is
(UB) in its generating-set-invariant reading. Only the literal
all-generating-sets reading needs Corollary 3.1. Superadditivity of Dehn
functions up to `≃` is open (Guba–Sapir), so that `K` cannot be removed for
free in general.

**Scope beyond Theorem C.** Let `G = ⟨t⟩ ≅ ℤ`. Let `X` be the union of the
triangles `[u, v, w_k]`, `k ∈ ℤ`, with `t` fixing `u` and `v` and sending
`w_k` to `w_{k+1}`. `X` is contractible and the action is cocompact. The edge
`[u, v]` has stabilizer `ℤ`, and the triangles have trivial stabilizers. So
Theorem C does not apply, but `X_∞ = [u, v]` and Theorem A does. The examples
that matter are in §5.

## 4. A commensurator criterion for finite clusters

**Corollary B.** Let `G ↷ X` be as in (S). Assume:

- (i) every edge `e = [u, v]` with `G_e` infinite has `[G_u : G_e] < ∞` and
  `[G_v : G_e] < ∞`;
- (ii) every vertex `x` with `G_x` infinite has `[Comm_G(G_x) : G_x] < ∞`.

Then every component of `X_∞` is finite. So (A) holds, together with
Corollaries 3.1 and 3.2.

*Proof.* Let `C` be a component of `X_∞` and `x ∈ C^(0)`, with `H = G_x`.

- Every vertex of `C` lies in a closed cell with infinite stabilizer, so its
  own stabilizer is infinite. By Lemma 1(c) and (i), adjacent vertices of `C`
  have commensurable stabilizers. `C^(1)` is connected, so every `G_y` with
  `y ∈ C^(0)` is commensurable with `H`.
- If `g ∈ G_C`, then `gx ∈ C`, so `g H g⁻¹ = G_{gx}` is commensurable with
  `H`, and `g ∈ Comm_G(H)`. So `H ≤ G_C ≤ Comm_G(H)` (Lemma 1(a)), and
  `[G_C : H] < ∞` by (ii).
- For `y ∈ C^(0)`,
  `[G_C : G_y] ≤ [G_C : G_y ∩ H] = [G_C : H] · [H : G_y ∩ H] < ∞`. So every
  `G_C`-orbit in `C^(0)` is finite. By Lemma 1(b) there are finitely many such
  orbits. So `C^(0)` is finite, and hence so is `C`. ∎

## 5. Baumslag–Solitar groups `BS(1, q)`

Let `q ≥ 2` and `G = BS(1, q) = ⟨a, t | t a t⁻¹ = a^q⟩ = A ⋊ ℤ`, with
`A = ℤ[1/q]`, `t` acting by multiplication by `q`, and `π : G → ℤ` the
projection. Write elements as `(a, s)` with
`(a, s)(b, r) = (a + q^s b, s + r)`.

**Theorem.** Under (N), every action of `G` in setting (S) satisfies (UB).

*Proof.* Three cases, by the vertex stabilizers `H = G_x`.

**Case 1: some `H` has `H ∩ A ≠ 0` and `π(H) ≠ 0`.** Pick `(u, 0) ∈ H` with
`u ≠ 0`, and `(w, k) ∈ H` with `k ≠ 0`. Conjugating by `(w, k)^j` gives
`(q^{jk} u, 0) ∈ H` for all `j ∈ ℤ`. So `H ∩ A ⊇ u ℤ[1/q^{|k|}] = u ℤ[1/q]`.
Write `u = p / q^r` with `p ∈ ℤ`. Then `u ℤ[1/q] = p ℤ[1/q]` has index at most
`|p|` in `A`. Also `π(H)` has finite index in `ℤ`, so `[G : H] < ∞`.

By Alonso, `δ_H ≃ δ_G`. Under (N),
`dist_X‾(δ_X(n)) ≥ n` and `δ_X(n) ≥ 1`, so the right-hand side of (UB) is
`≥ δ_H(n) ≽ δ_G(n)`.

**Case 2: some `H ≠ 1` has `π(H) = 0`.** `H` is finitely presented, so it is a
finitely generated subgroup of `ℤ[1/q]`. It is therefore cyclic, `H = ⟨u⟩`.
Now `u^{q^j} = t^j u t⁻ʲ` has `ℓ_G ≤ 2j + ℓ_G(u)` and `ℓ_H = q^j`. So
`dist^G_H(m) ≥ q^{(m − ℓ_G(u))/2}` for `m ≥ ℓ_G(u)`, and `dist_X(n) ≽ e^n`.
Under (N), the right-hand side of (UB) is
`≥ δ_{G_x}(dist_X‾(δ_X(n))) ≥ dist_X(δ_X(n)) ≥ dist_X(n) ≽ e^n`.

It remains to see that `δ_G ≼ e^n`. Let `w` be a null-homotopic word of
length `n`.

- Freely, `w` is a product of at most `n` conjugates `t^{p} a^{±1} t^{−p}`
  with `|p| ≤ n`, since the `t`-exponent sum of `w` is `0`.
- Conjugating by `t^n` does not change the area, and gives exponents
  `0 ≤ p ≤ 2n`.
- `t a^m t⁻¹ → a^{q m}` costs `m` relators. So `t^p a t^{−p} → a^{q^p}` costs
  at most `q^p`.
- The result is a word in `a` that is trivial in `G`. `⟨a⟩ ≅ ℤ`, so that word
  is freely trivial.

So the area is at most `n q^{2n}`, and `δ_G ≼ e^n`. (This is the classical
exponential upper bound.)

**Case 3: otherwise.** Every `H` has `H ∩ A = 0`, so `π|_H` is injective, and
`H` is trivial or `H = ⟨(w, k)⟩` with `k ≠ 0`. We check Corollary B.

- **(i).** If `G_e ≤ G_u` are both infinite cyclic, the index is finite.
- **(ii).** Let `H = ⟨h⟩`, `h = (w, k)`, `k ≠ 0`, and let `g = (v, 0)` lie in
  `A ∩ Comm_G(H)`. Then `g h^m g⁻¹ ∈ H` for some `m ≠ 0`. Applying `π` gives
  `g h^m g⁻¹ = h^m`. With `h^m = (w_m, mk)`:

  ```text
  g h^m g⁻¹ = (v + w_m − q^{mk} v, mk),
  ```

  so `v (1 − q^{mk}) = 0` and `v = 0`. So `π` is injective on `Comm_G(H)`,
  and `[Comm_G(H) : H] = [π(Comm_G(H)) : kℤ] ≤ |k|`.

By Corollary B, Theorem A applies. Vertex groups are trivial or `ℤ`, with
normalized Dehn function `m`, which is doubling. So Corollary 3.1 gives (UB)
literally, for every generating set. Explicitly, `δ_G ≼ δ_X(n)²`. ∎

Nothing in Case 3 forces `[G_e : G_σ] < ∞`: an infinite cyclic `G_e` may lie
in 2-simplices with trivial stabilizer, as in the `ℤ`-example of §3. So Case 3
is not covered by Theorem C. Case 2 is not covered by it either; there (UB)
comes from distortion alone.

## 6. What this says about the open hole

For `some-action-violates-dehn-bound-without-finite-index-faces`:

- A counterexample to (UB), even in the generating-set-invariant reading of
  Corollary 3.2, needs a component of `X_∞` that is infinite. Equivalently,
  the infinite-stabilizer cells must percolate. Products of trees and the
  `BS(1, q)` Case 2 actions have this, but the first has `κ_X` linear and the
  second satisfies (UB) by distortion.
- When (i) of Corollary B holds, a counterexample also needs a vertex
  stabilizer of infinite index in its commensurator. Then `G_C` is a
  non-trivial "cluster group" that is not virtually a vertex group.
- The natural next step is an infinite-cluster version. `G_C` acts on `C`
  with finitely many orbits (Lemma 1(b)), but `C` need not be simply
  connected, and `δ_{G_C}` is not controlled by the data in (UB). A
  counterexample must make `δ_{G_C}` large while `δ_X`, the `δ_{G_v}` and the
  distortions stay small.
