# Planar Rips complexes of infinite sets: free first homology and a chain-gadget reduction (2026-09-16)

This artifact belongs to swarm work on
`some-infinite-planar-set-has-a-non-wedge-rips-complex` (Zaremsky Problem 4.2).
It holds the full proofs behind two nodes:

- the route `planar-rips-complexes-have-free-first-homology-proof` (Theorem A);
- the route `infinite-non-wedge-from-a-multiplying-chain-gadget` (Theorem D),
  together with the constraints listed in the `## Attempts` of
  `some-planar-rips-chain-gadget-multiplies-a-sphere-class`.

Contents:

1. Conventions
2. Theorem A: `H_1` is free
3. Theorem D: a multiplying chain gadget gives non-free `H_2`
4. Constraints on gadgets
5. A purity criterion (positive direction)
6. Fundamental groups
7. Computation
8. Literature

## 1. Conventions

- `X ⊆ R^2` is a set and `r > 0` a scale. `R(X) = R_r(X)` is the simplicial
  complex on `X` whose simplices are the finite nonempty `σ ⊆ X` with
  `diam σ ≤ r` (closed convention) or `diam σ < r` (strict convention). It is
  the clique complex of the graph "distance `≤ r`" (resp. `< r`).
- For `Y ⊆ X`, `R(Y)` is the full subcomplex on `Y`. Full subcomplexes
  satisfy `R(Y) ∩ R(Y′) = R(Y ∩ Y′)`.
- Homology is singular homology of the geometric realization, with integer
  coefficients unless stated otherwise. It agrees with simplicial homology.
- For finite `F`, the closed complex `R_r(F)` equals the strict complex
  `R_{r′}(F)` for any `r′` strictly between `r` and the least distance in `F`
  exceeding `r`. So statements about finite sets hold in both conventions.
- For finite `F`, `p_F : |R(F)| → R^2` is the affine extension of the
  inclusion `F ⊆ R^2`. Its image `S(F) = p_F(|R(F)|)` is the *shadow*, a
  finite union of points, segments and triangles.

## 2. Theorem A

**Theorem A.** For every `X ⊆ R^2` and every `r > 0`, in either convention,
`H_1(R_r(X); Z)` is isomorphic to a subgroup of `C(Ω, Z)` for some profinite
space `Ω`. In particular it is a free abelian group.

### A1. Colimit

Every compact subset of `|R(X)|` lies in a finite subcomplex, and every finite
subcomplex lies in some `R(F)` with `F ⊆ X` finite. Singular chains and their
bounding chains have compact support. So

`H_1(R(X)) = colim_F H_1(R(F))`,

over the directed set of finite `F ⊆ X`, with inclusion-induced maps.

### A2. Shadows

Import `planar-rips-projection-is-a-pi1-isomorphism` (Chambers, de Silva,
Erickson and Ghrist, as restated in AFV Theorem 1.3). It says `p_F` induces a
bijection on `π_0` and an isomorphism on `π_1` at every basepoint.

Consequences:

- By Hurewicz on each component, `p_{F*} : H_1(R(F)) → H_1(S(F))` is an
  isomorphism.
- For `F ⊆ F′`, the map `p_{F′}` restricts to `p_F` on `|R(F)|`. So
  `S(F) ⊆ S(F′)`, and `p_{F′*} ∘ incl_* = incl_* ∘ p_{F*}`.

Therefore `H_1(R(X)) ≅ colim_F H_1(S(F))`, with maps induced by the inclusions
of shadows.

### A3. Winding numbers of a compact planar polyhedron

Let `K ⊆ R^2` be a finite union of points, segments and triangles. Let `W(K)`
be the finite set of bounded components of `R^2 ∖ K`.

**Definition.** For `p ∉ K`, let `wind_p : H_1(K) → H_1(R^2 ∖ {0}) = Z` be
induced by `y ↦ y − p`.

- `wind_p` depends only on the component of `R^2 ∖ K` containing `p`. A path
  `p_t` in `R^2 ∖ K` gives a homotopy of maps `K → R^2 ∖ {0}`.
- `wind_p = 0` if `p` lies in the unbounded component. Move `p` outside a
  closed disk `D_0 ⊇ K`; then `y ↦ y − p` factors through the contractible
  set `D_0 − p ⊆ R^2 ∖ {0}`.

Define `ω_K = (wind_{p_U})_{U ∈ W(K)} : H_1(K) → Z^{W(K)}`, where `p_U ∈ U`.

**Claim.** `ω_K` is an isomorphism.

*Triangulation.* Choose a closed triangle `D` with `K ⊆ int D`. Triangulate
`D` so that `K` is a subcomplex. For example, cut `D` by the lines through all
sides of the given segments and triangles, plus a horizontal and a vertical
line through every vertex (so that isolated points of `K` become arrangement
vertices). Every given point, segment and triangle is then a union of closed
cells of this arrangement of convex polygons. Triangulate each 2-cell by coning
from an interior point over its boundary, subdivided at all arrangement
vertices on it. (Referee edit 2026-09-16: the original text used only
horizontal lines and vertex fans, which can miss isolated points and produce
degenerate triangles.)

Work with simplicial chains, triangles oriented counterclockwise. The open
cells of the triangulation partition `D`, and `K` is a union of open cells.
So `int e ⊆ R^2 ∖ K` for every cell `e ∉ K`. For a triangle `t` and a point
`p ∉ ∂t`, `wind_p(∂t) = 1` if `p ∈ int t` and `0` otherwise.

*Injective.*

1. Let `c` be a simplicial 1-cycle of `K` with `ω_K[c] = 0`.
2. `D` is contractible, so `c = ∂σ` for a 2-chain `σ = Σ_t σ_t t` of `D`.
3. For a triangle `t`, pick `p_t ∈ int t`. This point lies on no edge, and in
   no other closed triangle. So `wind_{p_t}(c) = Σ_s σ_s wind_{p_t}(∂s) = σ_t`.
4. If `t ∉ K`, then `p_t ∉ K`. It lies either in a bounded component `U`,
   where `wind = ω_K[c]_U = 0`, or in the unbounded component, where
   `wind = 0`. So `σ_t = 0`.
5. Hence `σ` is a chain of `K`, and `[c] = 0` in `H_1(K)`.

*Surjective.*

1. For `U ∈ W(K)`, put `σ_U = Σ_{t : int t ⊆ U} t`.
2. Let `e` be an edge of `D` with `e ∉ K`. The triangles containing `e` are
   not in `K`, since `K` is closed under faces. Their interiors together with
   `int e` form a connected set disjoint from `K`, so they lie in one
   component.
3. If `e` is interior to `D`, its two triangles are both in `σ_U` or both
   not. They induce opposite orientations on `e`, so the coefficient of `e` in
   `∂σ_U` is `0`.
4. If `e ⊆ ∂D`, its only triangle `t` has `int t ∪ int e` connected to
   `R^2 ∖ int D`. That set is connected, unbounded and disjoint from `K`. So
   `int t` lies in the unbounded component and `t ∉ σ_U`.
5. Hence `∂σ_U` is a 1-cycle of `K`.
6. Let `V ∈ W(K)`. Then `V ⊆ int D`, because `R^2 ∖ int D` lies in the
   unbounded component.
7. `V` is open and nonempty, and the open cells of dimension `≤ 1` form a
   nowhere dense set. So `V` meets `int t_V` for some triangle `t_V`. That
   triangle is not in `K`, so `int t_V` is connected in `R^2 ∖ K` and
   `int t_V ⊆ V`.
8. With `p_V ∈ int t_V`,
   `wind_{p_V}(∂σ_U) = #{t ∈ σ_U : p_V ∈ int t} = [V = U]`.
9. So `ω_K[∂σ_U]` is the basis vector `e_U`.

### A4. Naturality

Let `K ⊆ L` be compact polyhedra.

- Put `P(K) = W(K) ⊔ {∞}`.
- Every `V ∈ W(L)` lies in a unique component of `R^2 ∖ K`. Let `π(V)` be that
  component if it is bounded, and `∞` otherwise. Put `π(∞) = ∞`.
- Identify `Z^{W(K)}` with the maps `f : P(K) → Z` with `f(∞) = 0`.

**Claim.** `ω_L ∘ incl_* = π^* ∘ ω_K`, where `π^* f = f ∘ π`.

For `x ∈ H_1(K)` and `p_V ∈ V`, `wind_{p_V}(incl_* x)` is `wind_{p_V}(x)`.
This equals `ω_K(x)_{π(V)}` if `π(V)` is bounded, and `0` otherwise, by the two
facts in A3. For `K ⊆ L ⊆ M` we have `π_{KL} ∘ π_{LM} = π_{KM}`.

### A5. Profinite embedding

For finite `F ⊆ F′ ⊆ X`, write `P(F) = P(S(F))` and
`π_{FF′} : P(F′) → P(F)`. Write `Z_0^P` for the pointed maps
`(P, ∞) → (Z, 0)`.

By A1–A4, `H_1(R(X)) ≅ colim_F Z_0^{P(F)}`, with transition maps `π_{FF′}^*`.

Let `Ω = lim_F P(F)`. It is a closed subspace of `∏_F P(F)` with finite
discrete factors, hence profinite. Write `pr_F` for its projections.

Define `Φ : colim_F Z_0^{P(F)} → C(Ω, Z)` by `[f] ↦ f ∘ pr_F`. It is well
defined because `pr_F = π_{FF′} ∘ pr_{F′}`.

**Claim.** `Φ` is injective.

1. Let `f ∈ Z_0^{P(F)}` with `f ∘ pr_F = 0`.
2. For `F′ ⊇ F`, the images `I_{F′} = π_{FF′}(P(F′)) ⊆ P(F)` decrease as `F′`
   grows. Pick `F*` minimizing `|I_{F*}|`. Then `I_{F′} = I_{F*}` for every
   `F′ ⊇ F*`.
3. Let `a ∈ I_{F*}`. For finite `G ⊇ F*`, the set `Q_G = π_{FG}^{-1}(a) ⊆ P(G)`
   is nonempty, and the transition maps send `Q_{G′}` into `Q_G`.
4. An inverse limit of nonempty finite sets over a directed set is nonempty.
   The compatibility conditions are closed in the compact product `∏ Q_G`, and
   they have the finite intersection property because the index set is
   directed.
5. The sets `G ⊇ F*` are cofinal. So a point of `lim Q_G` is a point `ω ∈ Ω`
   with `pr_F(ω) = a`.
6. Hence `I_{F*} ⊆ pr_F(Ω)`. So `f` vanishes on `I_{F*}`, that is,
   `π_{FF*}^* f = 0`, and `[f] = 0`.

### A6. Freeness

**Nöbeling's theorem.** For every profinite space `S`, the group `C(S, Z)` is
free abelian. It is imported as the claim
`profinite-integer-function-groups-are-free`. The statement was read on
2026-09-16 in D. Asgeirsson, "Towards solid abelian groups: A formal proof of
Nöbeling's theorem", arXiv:2309.07252v2, §4, Theorem 18. The original 1968
paper by Nöbeling was not opened.

Subgroups of free abelian groups are free. So `H_1(R(X))` is free. ∎

### Remarks

- A point of `Ω` is a compatible choice, at every finite stage, of a hole of
  the shadow or `∞`.
- The theorem rules out `H_1` as a non-wedge certificate for infinite planar
  sets. A certificate must use `π_1` beyond its abelianization, `H_q` with
  `q ≥ 2`, or finer structure.

## 3. Theorem D

### Hypothesis (Gad)

Fix a finite `G ⊆ R^2`, a scale `r > 0`, a vector `v ≠ 0` with translation
`τ(x) = x + v`, a subset `A ⊆ G`, a class `z ∈ H_2(R(A))`, and an integer `m`
with `|m| ≥ 2`. Use the closed convention. Put `B = τ(A)`, write
`i_A : R(A) → R(G)` and `i_B : R(B) → R(G)` for the inclusions, and let
`τ_* : H_2(R(A)) → H_2(R(B))` be induced by the simplicial isomorphism `τ|_A`.

- (G0) `R(G)` is connected.
- (G1) `B ⊆ G` and `A ∩ B = ∅`.
- (G2) *Separation.* If `x ∈ G ∖ B`, `y ∈ τ^k(G)` for an integer `k ≥ 1`, and
  `|x − y| ≤ r`, then `k = 1` and `y ∈ B`.
- (G3) The kernel of `i_{A*} : H_2(R(A)) → H_2(R(G))` is a torsion group.
- (G4) `a := i_{A*}(z)` has infinite order, and
  `a = m · i_{B*}(τ_* z)` in `H_2(R(G))`.

(G2) is a finite condition, since it holds automatically once
`|k v| > diam G + r`.

**Theorem D.** Assume (Gad) and put `X = ∪_{k ≥ 0} τ^k(G)`. Then:

- `X` is infinite;
- `R_r(X)` is connected;
- `H_2(R_r(X); Z)` contains a nonzero element divisible by `m^k` for every
  `k`.

So `H_2` is not free, and `R_r(X)` is not homotopy equivalent to a wedge of
spheres. The same holds for the strict complex `R_{r+ε}(X)` for small `ε > 0`.

### D1. Levels

Put `G_k = τ^k(G)` and `L_k = τ^k(G ∖ B)` for `k ≥ 0`.

**(S) Separation lemma.** If `x ∈ L_j`, `y ∈ G_k` with `k > j`, and
`|x − y| ≤ r`, then `k = j + 1` and `y ∈ τ^j(B)`.

*Proof.* Apply (G2) to `τ^{−j}x ∈ G ∖ B` and `τ^{−j}y ∈ τ^{k−j}(G)`.

Consequences:

- **(a) The levels cover `X`.** `A ⊆ G ∖ B` by (G1), so
  `τ^k(B) = τ^{k+1}(A) ⊆ L_{k+1}`. Hence `G_k = L_k ∪ τ^k(B) ⊆ L_k ∪ L_{k+1}`
  and `X = ∪_k L_k`.
- **(b) The levels are disjoint.** A common point of `L_j` and `L_k ⊆ G_k`
  with `j < k` has distance `0 ≤ r` from itself. By (S) it lies in
  `L_j ∩ τ^j(B) = τ^j((G ∖ B) ∩ B) = ∅`.
- **(c) Intersections of copies.** `G_j ∩ G_k = ∅` for `k ≥ j + 2`, and
  `G_j ∩ G_{j+1} = τ^j(B)`.
  - The first follows from (a) and (b).
  - For the second: by (b), `G_j ∩ G_{j+1} ⊆ L_{j+1}`, and
    `G_j ∩ L_{j+1} = τ^j(B)`. Conversely `τ^j(B) = τ^{j+1}(A) ⊆ G_{j+1}`.
- **(d) `X` is infinite.** The sets `L_k ⊇ τ^k(A)` are nonempty and pairwise
  disjoint. `A ≠ ∅` because `H_2(R(A)) ∋ z ≠ 0`.

### D2. Every simplex lies in one copy

Let `σ` be a simplex of `R(X)`, and let `j` be the least `k` with
`σ ∩ L_k ≠ ∅`. Pick `x ∈ σ ∩ L_j`.

Each `y ∈ σ` lies in some `L_k ⊆ G_k` with `k ≥ j`. If `k > j`, then (S)
gives `y ∈ τ^j(B)`. So `σ ⊆ L_j ∪ τ^j(B) = G_j`.

Put `Y_N = ∪_{k ≤ N} R(G_k)`. By D2 and (c):

- `Y_N = R(∪_{k ≤ N} G_k)`. A clique in the union lies in some `G_j`. If
  `j = N + 1`, it lies in `G_N ∩ G_{N+1} = τ^N(B) ⊆ G_N`, and `j > N + 1` is
  impossible by (c).
- `R(X) = ∪_N Y_N` and `Y_{N+1} = Y_N ∪ R(G_{N+1})`.
- `Y_N ∩ R(G_{N+1}) = R(τ^N(B)) = R(τ^{N+1}(A))`.
- `R(X)` is connected. Each `R(G_k) ≅ R(G)` is connected by (G0), and
  consecutive copies share `τ^N(B) ≠ ∅`.

### D3. Divisibility

Put `z_k = τ^k_* z ∈ H_2(R(τ^k A))`, and let `α_k ∈ H_2(R(X))` be its image.

The simplicial isomorphism `τ^k : R(G) → R(G_k)` carries `R(A)` to `R(τ^k A)`
and `R(B)` to `R(τ^{k+1} A)`. Applying `τ^k_*` to (G4) inside `H_2(R(G_k))`:

(image of `z_k`) `= m ·` (image of `z_{k+1}` under `R(τ^{k+1}A) ⊆ R(G_k)`).

Pushing forward to `R(X)` gives `α_k = m α_{k+1}`, so `α_0 = m^k α_k` for every
`k`.

### D4. Non-vanishing

`Q` is a divisible, hence injective, `Z`-module. So a homomorphism from a
subgroup into `Q` extends to the whole group. We build
`φ_N : H_2(Y_N) → Q` with `φ_{N+1} ∘ j_N = φ_N` and `φ_0(a) = 1`, where
`j_N : H_2(Y_N) → H_2(Y_{N+1})`.

*Start.* `⟨a⟩ ≅ Z` by (G4). Send `a ↦ 1` and extend to `H_2(Y_0) = H_2(R(G))`.

*Step.* Put `C = R(τ^{N+1} A) = Y_N ∩ R(G_{N+1})`, with inclusions `i : C → Y_N`
and `i′ : C → R(G_{N+1})`, and let `j′ : H_2(R(G_{N+1})) → H_2(Y_{N+1})` be
induced by inclusion.

1. Mayer–Vietoris gives an exact sequence
   `H_2(C) → H_2(Y_N) ⊕ H_2(R(G_{N+1})) → H_2(Y_{N+1})`, with maps
   `(i_*, −i′_*)` and `j_N + j′`.
2. `i′` is conjugate to `i_A` by `τ^{N+1}`, so `ker i′_*` is torsion by (G3).
   `φ_N ∘ i_*` vanishes on torsion, because `Q` is torsion-free.
3. So `ψ(i′_* c) := φ_N(i_* c)` is a well-defined homomorphism on `im i′_*`.
   Extend it to `H_2(R(G_{N+1}))`.
4. `Λ(x, y) = φ_N(x) + ψ(y)` vanishes on `im(i_*, −i′_*) = ker(j_N + j′)`. So
   it induces a homomorphism on `im(j_N + j′) ⊆ H_2(Y_{N+1})`.
5. Extend that to `φ_{N+1}`. Then `φ_{N+1}(j_N x) = Λ(x, 0) = φ_N(x)`.

*Conclusion.* `H_2(R(X)) = colim_N H_2(Y_N)` as in A1. So the `φ_N` define
`φ : H_2(R(X)) → Q` with `φ(α_0) = φ_0(a) = 1`, and `α_0 ≠ 0`.

### D5. Not a wedge

- In a free abelian group, an element divisible by `m^k` for every `k` (with
  `|m| ≥ 2`) is `0`: look at a nonzero coordinate.
- By D3 and D4, `H_2(R(X))` has such an element that is nonzero. So it is not
  free.
- A wedge of spheres has free integral homology, since its cellular chain
  complex has zero differentials.
- `R(X)` is connected by D2. So it is not homotopy equivalent to a wedge of
  spheres.

### D6. Strict convention

For `x, y ∈ G` and integers `k`, the inequality `|x − y + k v| ≤ r + 1` holds
for only finitely many triples. So the set of distances of `X` in `[0, r + 1]`
is finite. Choose `0 < ε < 1` below the gap between `r` and the next larger
distance. Then the strict complex `R_{r+ε}(X)` equals the closed complex
`R_r(X)`. ∎

### D7. Variants

The proofs carry over verbatim.

1. **(G4) up to torsion.** Suppose `a − m · i_{B*}(τ_* z)` is only a torsion
   element. Then `α_k − m α_{k+1}` is torsion in `H_2(R(X))`. Either
   `H_2(R(X))` has torsion, and is not free, or the relations are exact.
   `φ(α_0) = 1` still holds.
2. **Non-periodic chains.** Take finite sets `G_0, G_1, …` with the following
   properties:
   - `G_j ∩ G_k = ∅` for `|j − k| ≥ 2`;
   - every clique of `∪ G_k` lies in one `G_k`;
   - ports `P_k = G_{k−1} ∩ G_k` for `k ≥ 1` and a chosen `P_0 ⊆ G_0`;
   - classes `z_k ∈ H_2(R(P_k))` whose images satisfy
     `image(z_k) = m_k · image(z_{k+1})` in `H_2(R(G_k))`;
   - the image of `z_0` has infinite order;
   - `ker(H_2(R(P_k)) → H_2(R(G_k)))` is torsion for `k ≥ 1`;
   - `|m_0 m_1 ⋯ m_k| → ∞`.

   Then `H_2(R(∪ G_k))` is not free.

## 4. Constraints on gadgets

### 4.1 Relative torsion

**Lemma.** Assume (Gad) and `H_2(R(A)) = Z z`. For example, `A` is an
octahedral hexagon and `R(A)` is the boundary of the octahedron. Put
`b = i_{B*}(τ_* z)`. Then `b̄ ∈ coker(i_{A*})` is nonzero with `m b̄ = 0`.

*Proof.* `m b = a ∈ im i_{A*}`, so `m b̄ = 0`. If `b̄ = 0`, then `b = k a` for
some integer `k`, so `a = m k a` and `(1 − m k) a = 0`. Since `m k ≠ 1` and `a`
has infinite order, this is impossible.

The exact sequence of the pair `(R(G), R(A))` gives

`0 → coker(i_{A*}) → H_2(R(G), R(A)) → ker(H_1(R(A)) → H_1(R(G))) → 0`.

The right-hand group is a subgroup of the free group `H_1(R(A))`. So the
torsion of `H_2(R(G), R(A))` equals the torsion of `coker(i_{A*})`.

Also `H_2(R(G), R(A)) ≅ H_2(R(G) ∪ cone R(A))`. This cofibre is the clique
complex of the `r`-graph on `G` plus one abstract vertex joined to `A`.

So a gadget with `H_2(R(A)) = Z z` forces torsion in `H_2` of that flag
complex. Section 7 searches for exactly this.

**Lemma 4.1′ (any port rank; referee addition 2026-09-16).** Assume (Gad), and
assume `H_2(R(A); Z)` is torsion-free. Then `coker(i_{A*})` has a nonzero
element of order dividing `m`. Hence `H_2(R(G), R(A))` has torsion.

*Proof.*

1. By (G3) and torsion-freeness, `i_{A*}` is injective. `z ≠ 0`, because
   `a = i_{A*} z` has infinite order.
2. Suppose `coker(i_{A*})` has no nonzero element killed by `m`. Put
   `w_0 = z`, and assume that `w_k` satisfies
   `i_{A*} w_k = m · i_{B*}(τ_* w_k)`.
3. The class `b_k = i_{B*}(τ_* w_k)` satisfies `m b_k ∈ im i_{A*}`. So
   `b̄_k` is killed by `m`, and by assumption `b̄_k = 0`. Write
   `b_k = i_{A*} w_{k+1}`.
4. Then `i_{A*} w_k = m b_k = i_{A*}(m w_{k+1})`, so `w_k = m w_{k+1}` by
   injectivity.
5. Applying the homomorphism `i_{B*} τ_*` to `w_k = m w_{k+1}` gives
   `m · i_{B*}(τ_* w_{k+1}) = i_{B*}(τ_* w_k) = b_k = i_{A*} w_{k+1}`. So the
   relation of step 2 holds for `w_{k+1}`.
6. Hence `z = m^k w_k` for all `k`. But `H_2(R(A))` is finitely generated and
   torsion-free, hence free, and `z ≠ 0` with `|m| ≥ 2`. Contradiction. ∎

If `H_2(R(A))` has torsion, then some component of `R(A)` (a connected Rips
complex of a finite planar set) has torsion in `H_2`. That already settles
`some-finite-planar-set-has-a-non-wedge-rips-complex`. So, unless the finite
question is already settled by a component of the port, every gadget forces
torsion in `H_2(R(G), R(A)) ≅ H_2(R(G) ∪ cone R(A))`.

### 4.2 A coneable port gives a finite counterexample

Suppose some `p ∈ R^2 ∖ G` satisfies `{g ∈ G : |g − p| ≤ r} = A`. Then
`R(G ∪ {p}) = R(G) ∪ (p * R(A))`, with intersection `R(A)`.

Mayer–Vietoris gives
`0 → coker(i_{A*}) → H_2(R(G ∪ {p})) → ker(H_1(R(A)) → H_1(R(G))) → 0`.

The right-hand group is free. Under 4.1, or under 4.1′ when `H_2(R(A))` is
torsion-free, the left-hand group has nonzero torsion. So `H_2(R(G ∪ {p}))` has
torsion. `R(G ∪ {p})` is connected, since `A ≠ ∅` and `R(G)` is connected, so
it is not a wedge. If `H_2(R(A))` has torsion, a component of `R(A)` is already
a finite non-wedge. Either way this resolves
`some-finite-planar-set-has-a-non-wedge-rips-complex`.

So a gadget matters for the infinite question independently only if no port
is coneable.

### 4.3 One-point extensions keep images pure

Let `F` be finite, `w ∉ F`, and `Z = {x ∈ F : |x − w| ≤ r}`. Then
`R(F ∪ {w}) = R(F) ∪ (w * R(Z))`, and Mayer–Vietoris gives

`0 → coker(H_2(R(Z)) → H_2(R(F))) → H_2(R(F ∪ {w})) → ker(H_1(R(Z)) → H_1(R(F))) → 0`.

- The quotient `H_2(R(F ∪ {w})) / im H_2(R(F))` is a subgroup of the free group
  `H_1(R(Z))`, so it is torsion-free.
- So the image of `H_2(R(F))` in `H_2(R(F ∪ {w}))` is pure.

Purity is not preserved under composition. For example, `Z(1, 0) ⊆ Z^2` is
pure, and the map `Z^2 → Z`, `(x, y) ↦ 2x + y`, has pure image, but sends
`Z(1, 0)` to `2Z`. So non-purity of `im i_{A*}` needs several added points
acting together; it never comes from the last point alone.

### 4.4 Sliding gives `m = ±1`

Let `O` be the octahedral sphere of a 6-point set with antipodal far pairs
`{a_1, a_4}`, `{a_2, a_5}`, `{a_3, a_6}`, so `O = (a_1 − a_4) * L`, where `L` is
the 4-cycle on `a_2, a_3, a_5, a_6`.

Suppose `a_1′` is within `r` of `a_1` and `{a_1′, a_2, …, a_6}` is again
octahedral, with sphere `O′`. The tetrahedra `{a_1, a_1′, x, y}` for edges `xy`
of `L` are cliques. So `O − O′ = (a_1 − a_1′) * L = −∂((a_1 a_1′) * L)`, and
`O` is homologous to `O′`.

Sliding a sphere along a track therefore carries `a` to `±b`, never to a
proper multiple. A gadget needs a genuinely different mechanism.

The most obvious local mechanism for `m = 2` does not occur in the plane.

- The flag complex `S^0 * S^0 * Ind(K_3)` has the relation
  `O_{13} = O_{12} + O_{23}` among its three octahedra. Here `Ind(K_3)` is three
  pairwise non-adjacent vertices, and `O_{ij}` is the octahedron on the two
  `S^0`'s and the vertices `i`, `j`.
- Combined with a slide `O_{12} ∼ O_{23}`, this relation would give `m = 2`.
- By Lemma 4.6 below, no planar Rips complex contains `S^0 * Ind(K_3)` as an
  induced subcomplex. So `S^0 * S^0 * Ind(K_3)` is not an induced subcomplex
  either.

### 4.5 Relation with the circle construction

Attempt (B) of `some-finite-planar-set-has-a-non-wedge-rips-complex` needs the
same local relation between neighbouring spheres, with multiplicities of
different absolute value, and closes the chain up by a rotation. Theorem D
needs no closing up. The obstacle recorded there applies unchanged: carrying a
sphere needs steps below `r`, while separation needs steps above `r`.

### 4.6 Common neighbourhoods of a far pair

Call `x, y` *near* if `|x − y| ≤ r` and *far* otherwise. In the strict
convention, read `< r` and `≥ r`; every inequality below changes the same way.

**Lemma 4.6.** Let `a, a′ ∈ R^2` be far. Let `p, q` both be near `a` and near
`a′`, with `p, q` far. Then:

- `a, p, a′, q` are in strictly convex position, in this cyclic order;
- the segments `a a′` and `p q` cross at a point interior to both;
- `p` and `q` lie strictly on opposite sides of the line `ℓ` through `a`
  and `a′`.

*Proof.*

1. *Distinct points.* The four points are distinct. For example, `p = a` is
   impossible because `p` is near `a′` and `a` is far from `a′`.
2. *Fact about triangles.* If `u` lies in the closed convex hull of `v, w, x`,
   then `|u − v| ≤ max(|v − w|, |v − x|)`, because the distance to `v` is a
   convex function.
3. *No point lies in the closed hull of the other three.*
   - If `q ∈ conv{a, p, a′}`, then `|q − p| ≤ max(|p − a|, |p − a′|) ≤ r`,
     but `p, q` are far. The case of `p` is symmetric.
   - If `a ∈ conv{p, a′, q}`, then `|a − a′| ≤ max(|a′ − p|, |a′ − q|) ≤ r`,
     but `a, a′` are far. The case of `a′` is symmetric.
   - So the four points are in strictly convex position.
4. *Crossing-diagonal inequality.* In a strictly convex quadrilateral, the
   sum of either pair of opposite sides is at most the sum of the diagonals.
   Apply the triangle inequality at the crossing point of the diagonals.
5. *`a a′` is a diagonal.* Suppose `a a′` were a side. Then `p q` is the
   opposite side, and each diagonal joins a point of `{a, a′}` to a point of
   `{p, q}`. So `|a − a′| + |p − q| ≤ 2r` by step 4, but the left side exceeds
   `2r`.
6. So `a a′` and `p q` are the diagonals. They cross at a point interior to
   both, and strict convexity keeps `p, q` off `ℓ`. ∎

**Corollary 4.6.1.**

- For every far pair `a, a′` of a planar set, the far graph on the common
  neighbourhood `N(a) ∩ N(a′)` is bipartite. Its two sides are the open
  half-planes of `ℓ`, and points on `ℓ` are isolated.
- In particular there are no five points `a, a′, p_1, p_2, p_3` with
  `a a′` far, `p_1, p_2, p_3` pairwise far, and all six cross pairs near.
- So `S^0 * Ind(K_3)` (far graph `K_2 ⊔ K_3`) is never an induced subcomplex
  of a planar Rips complex, and neither is `S^0 * S^0 * Ind(K_3)`.
- Every induced suspension `R({a, a′} ∪ M)` with `M ⊆ N(a) ∩ N(a′)` is the
  suspension of the independence complex of a bipartite graph.

This lemma is elementary and in the spirit of the crossing lemmas of CdSEG and
AFV. Referee check 2026-09-16: the lemmas of the CdSEG preprint
arXiv:0712.0395v1 (read in its LaTeX source) do not state it in this form.
Whether it appears in AFV was not checked.

**Numerical sanity check.** The script `far_k2_k3_search.py` maximizes the
minimal slack of the five-point pattern by hill climbing. With seeds 1 and 2
and 1500 restarts each, the best slacks were `−7.6 · 10^{−5}` and
`−6.1 · 10^{−5}`: the supremum is approached only in degenerate limits. As
calibration, the four-point square pattern reached slack `+0.17`. The output
is in `results-2026-09-16.txt`.

## 5. A purity criterion (positive direction)

**Lemma C.** Let `H` be a torsion-free abelian group that is the union of an
increasing sequence `S_0 ⊆ S_1 ⊆ …` of finitely generated subgroups, each pure
in `H`. Then `H` is free.

*Proof.*

1. `S_n` is pure in `S_{n+1}`, because `S_n ∩ k S_{n+1} ⊆ S_n ∩ k H = k S_n`.
2. So `S_{n+1}/S_n` is finitely generated and torsion-free, hence free, and
   `S_{n+1} = S_n ⊕ Q_{n+1}` for some complement `Q_{n+1}`.
3. `S_0` is free, and `H = S_0 ⊕ ⊕_{n ≥ 1} Q_n`. ∎

**Application.** Let `X` be countable, `X = ∪ F_n` with `F_n` finite and
increasing, and `q ≥ 2`. Suppose `H_q(R(X))` is torsion-free and each image
`im(H_q(R(F_n)) → H_q(R(X)))` is pure. Then `H_q(R(X))` is free.

A multiplying chain gadget is an instance of a failure of this purity: `α_0`
lies in the first image and is divisible by `m^k` in later ones.

Free homology does not certify a wedge. `CP^2` is simply connected with free
homology. So Lemma C is only a necessary-condition tool.

## 6. Fundamental groups

**Proposition.** For every `X ⊆ R^2` and `x_0 ∈ X`, `π_1(R(X), x_0)` is
locally free (every finitely generated subgroup is free). Its abelianization
is free by Theorem A.

*Proof.*

1. `π_1` commutes with directed unions of subcomplexes.
2. Fix finite `F ∋ x_0`. For `F′ ⊇ F`, the image
   `I_{F,F′} = im(π_1(R(F)) → π_1(R(F′)))` is finitely generated and lies in
   the free group `π_1(R(F′))`, so it is free.
3. For `F ⊆ F′ ⊆ F″`, the group `I_{F,F″}` is a quotient of `I_{F,F′}`. So the
   ranks do not increase; abelianize a surjection of free groups.
4. At a stage `F*` of minimal rank, every later surjection
   `I_{F,F*} → I_{F,F″}` is between free groups of equal finite rank. Free
   groups of finite rank are Hopfian, so these surjections are isomorphisms.
5. Hence the image of `π_1(R(F))` in `π_1(R(X))` is `I_{F,F*}`, free of finite
   rank.
6. `π_1(R(X))` is the directed union of these images, and subgroups of free
   groups are free. ∎

**Where freeness of `π_1` dies.** For countable `X`, `π_1(R(X))` would be free
if, along some exhaustion `F_n`, each image were a free factor of the next.

- For inclusions of connected planar compact polyhedra this looks plausible.
  Holes of `K` split into holes of `L`, and boundary loops become products of
  conjugates of distinct generators.
- It is not proved here. Purely algebraic composites fail: `x_1^2 x_n` is
  primitive in `F(x_1, x_n)`, but killing `x_n` leaves `x_1^2`.
- For uncountable `X`, even such a lemma would not suffice, because non-free
  `ℵ_1`-free groups exist.
- A non-free `π_1` would itself certify a non-wedge.

## 7. Computation

The script is
`experiments/zaremsky-4-02-planar-rips-comp-2026-09-16/relative_torsion_search.py`,
with output in `results-2026-09-16.txt` in the same directory. The same
directory holds `far_k2_k3_search.py`, the sanity check for Lemma 4.6.

**Method.**

1. For random `(G, r, A)`, build the clique complex of the `r`-graph on `G`
   plus a cone vertex joined to `A` (section 4.1).
2. Reduce it by dominated vertices and dominated edges. Both preserve the
   homotopy type of a clique complex.
3. Compute Betti numbers mod `2`, mod `3` and mod `1000003`. A difference
   certifies torsion.

**Calibration.**

- Regular hexagon at `r = 1.9`: `[1, 0, 1]`.
- Cofibre on 5 of its 6 points: `[1, 0, 1]`.
- Cofibre on all 6 points: `[1]`.

**Families.**

| Family | `G` | `A` |
|---|---|---|
| `hexcloud` | hexagon plus 3–8 random points, scales between consecutive distances in `[1.74, 1.99]` | the hexagon |
| `twohex` | two unit hexagons at distance 2.2–4.2 plus 2–7 random points, `r ∈ (1.74, 1.99)` | one hexagon, or both (`-both`) |
| `disk` | 8–13 random points in the unit disk | missing 2–4 points |
| `halfplane` | 9–14 random points | a half-plane |
| `hexdense` | hexagon plus 8–16 points | the hexagon |
| `chain` | hexagons `A` and `A + (D, 0)`, `D ∈ [2.2, 4.5]`, plus 6–14 strip points, `r ∈ (1.74, 1.99)` | one hexagon, or both (`-both`) |

The first four are the "basic" mode (seeds 1–4, 3000 each); `hexdense` and
`chain` are the "dense" mode (seeds 5–7, 4000 each).

**Result.** 24,000 relative complexes, none skipped for size. Nontrivial
relative homology occurred often: for example 1420 of 1970 `hexdense`
complexes in seed 5. In every complex the Betti numbers mod 2 and mod 3 agreed
with those mod 1000003, so no 2- or 3-torsion was detected; other primes were
not tested. This is evidence only. (Referee rerun 2026-09-16: seed 1 basic and
the Lemma 4.6 hill climb with seed 1 reproduced exactly; a flag triangulation
of `RP^2` is correctly flagged by the same Betti routine.) It is consistent with the 2026-09-13 absolute search
(`research/artifacts/zp-planar-rips-search-2026-09-13.md`).

## 8. Literature

External gate, 2026-09-16, arXiv API and listing pages:

- M. Adamaszek, F. Frick and A. Vakili, arXiv:1602.04131v1 (2016). Theorem 1.3
  restates CdSEG, and p. 2 says `π_1` freeness is the only known non-trivial
  information about planar Rips homotopy types.
- V. Sipani and R. Kasilingam, arXiv:2406.01082 (2024), "On the Classification
  of Planar-Rips complexes and their corresponding unit disk graphs":
  pseudomanifolds and weak pseudomanifolds. It does not address wedges.
- R. Komendarczyk, S. Majhi and A. Mitra, arXiv:2506.01603 (2025),
  "Vietoris--Rips Shadow for Euclidean Graph Reconstruction". Its abstract
  restates the CdSEG `π_0`/`π_1` theorem for planar sets and extends it to
  path-based metrics.
- K. Kawamura, S. Majhi and A. Mitra, arXiv:2601.01359 (2026), "The Shadow of
  Vietoris--Rips Complexes in Limits": shape-theoretic limits of shadow
  projections as `β → 0`. It does not address the fixed-scale infinite
  question.
- H. Adams et al., arXiv:2511.09471 (2025), ellipses at larger scales.
- H. Adams, A. Karassev and Ž. Virk, arXiv:2512.23108 (2025), Vietoris
  thickenings.
- S. Hulbert and M. Zaremsky, arXiv:2608.25614 (2026), Morse theory for
  Vietoris–Rips complexes of groups.
- D. Asgeirsson, arXiv:2309.07252v2 (2023), for the statement of Nöbeling's
  theorem.
- Zaremsky's problem list (version of 12 July 2026): Problem 4.2 is still
  listed as open.

None of these proves freeness of `H_1` for infinite planar sets or gives a
non-wedge planar Rips complex.
