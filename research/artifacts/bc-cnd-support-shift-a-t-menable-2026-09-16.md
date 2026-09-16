# CND-support shifts are a-T-menable: the tree boundary is K-amenable and the HLS class never lifts (2026-09-16)

Author: frontier swarm agent for `baum-connes-counterexample-group-exists`, 2026-09-16.

## 0. Results and dependencies

**Results.**
- **Theorem A** (`cnd-support-shift-actions-are-a-t-menable`). For a finitely generated group `G` and a finite alphabet,
  the shift action on every closed invariant set of nonzero configurations whose supports carry a conditionally negative
  definite word metric is a-T-menable in the sense of Baum--Guentner--Willett, Definition 6.1. The proof is elementary.
- **Theorem B** (`cnd-support-shift-bc-and-k-amenability`). For every such set `Z`, reduced and maximal assembly at
  `C_0(Z)` are isomorphisms, and `K_*(C_0(Z) ⋊_max G) -> K_*(C_0(Z) ⋊_r G)` is an isomorphism.
- **Theorem C** (route `expander-tree-boundary-k0-max-reduced-injective-proof`). Under (M), the nonzero tree-boundary
  configurations form such a set. So (H-K) holds, and in fact the max-to-reduced map is an isomorphism there.
- **Theorem D** (`hls-ghost-class-never-lifts-to-the-bernoulli-full-shift`). Under (M), with no hypothesis (H-K) and no
  forest-shift hypothesis (F), every full-shift class that vanishes on the tree boundary has `r_(x_n)(y) = 0` for all
  large `n`. So `hls-ghost-class-lifts-to-the-bernoulli-full-shift` is false.
- **Corollary E.** For every finitely generated torsion-free `G`, the cylinder classes over the CND-support shift form a
  `Z`-basis of `K_0(C_0(T_cnd \ {0}) ⋊_r G)`, and `K_1 = 0`.

**Graph dependencies.**
- `a-t-menable-actions-have-tu-dual-dirac-elements` (new citation claim; BGW arXiv:1311.2343v3, Section 6, quoting
  Tu 1999).
- `bernoulli-shift-weak-k-equivalence-and-going-down`, items 2 (going-down) and 3 (proper coefficients).
- `amenable-kernel-bc-transfer-and-ktop-half-exactness`, item 3 (half-exactness of `K^top`, naturality of assembly).
- `bernoulli-bc-splits-into-host-and-cylinder-comparison` (CC), item 4 (the cylinder form of the weak K-equivalence).
- `bernoulli-assembly-injective-beyond-the-host` (RF), item 1 and the pattern expansion `n(y)` of item 3.
- `bernoulli-pattern-expansions-are-finite` (LOC), Corollary 2 (unreviewed).
- Hypotheses (M) are those of `hls-ghost-lift-needs-forest-shift-failure`. Only the definitions are used. Lemma 1.1 of
  `research/artifacts/bc-bernoulli-hls-ghost-lift-2026-09-13.md` is reproved in Section 1.

**Context imports, not re-read.**
- Kasparov's descent homomorphisms `j_max, j_r : KK^G(A, B) -> KK(A ⋊_max G, B ⋊_max G), KK(A ⋊_r G, B ⋊_r G)` are
  functorial for Kasparov products (Kasparov, Invent. Math. 91 (1988)).
- Assembly is natural for `KK^G`-morphisms: `mu_B ∘ K^top(x) = j(x)_* ∘ mu_A` for `x ∈ KK^G(A, B)`, for both crossed
  products (Baum--Connes--Higson, Contemp. Math. 167 (1994)).
- Reduced assembly is maximal assembly followed by `λ_A : A ⋊_max G -> A ⋊_r G`. BGW, proof of Proposition 4.5, uses
  this description: "applying those in (2.3) followed by the map on K-theory induced by the natural transformation
  λ_A : A ⋊_max G -> A ⋊_τ G".

## 1. Setting and notation

- `G` is a finitely generated group with finite symmetric generating set `S` and left-invariant word metric `d`. Write
  `|g| = d(e, g)`.
- `Λ` is a finite set containing `0` with `|Λ| >= 2`. `X = Λ^G` carries the left shift `(g·x)(h) = x(g^(-1) h)`, and
  `X^0 = X \ {0}`. Then `supp(g·x) = g supp(x)`.
- BGW use right actions. We put `x g := g^(-1)·x`, so `supp(xg) = g^(-1) supp(x)`.
- A **pattern** is `s = (F, a)` with `F ⊆ G` finite nonempty and `a : F -> Λ \ {0}`. Its cylinder is
  `C_s = {y : y|_F = a}`, and `x_s ∈ X` is the configuration equal to `a` on `F` and `0` elsewhere. `S_pat` is the
  `G`-set of patterns. For a finite-support `x` and a pattern `t`, `t <= x` means `t = (F, x|_F)` with
  `∅ ≠ F ⊆ supp x`.
- **CND.** A symmetric kernel `k` on a set `P` with `k(p, p) = 0` is conditionally negative definite if
  `Σ_(i,j) t_i t_j k(p_i, p_j) <= 0` for all `p_1, ..., p_n ∈ P` and real `t_i` with `Σ t_i = 0`. Repetitions among the
  `p_i` are harmless: group equal points and add their coefficients.
- **The CND-support shift.**

  ```text
  T_cnd = { x ∈ X : d restricted to F is CND for every finite F ⊆ supp x }.
  ```

  Put `T_cnd^0 = T_cnd \ {0}`. Membership depends only on `supp x`.
- **Ranks.** For a pattern `x` (a nonzero finite-support configuration), `π_x` is the orbit representation of
  `C_0(X^0) ⋊_r G` on `ℓ^2(G·x)`. RF item 1: it maps into the compacts, and `r_x = K_0(π_x)`. RF Lemma R2:
  `r_x[1_(C_s)] = #{t <= x : t ∈ G s}`. The pattern expansion `n(y)` is the Möbius inverse of the ranks:
  `r_x(y) = Σ_(t <= x) n_([t])(y)`.

**Hypotheses (M)** (of `hls-ghost-lift-needs-forest-shift-failure`).
- `G` is torsion-free.
- `X_n` are finite connected `D`-regular graphs, `D >= 3`, with spectral gap `ε`, `girth(X_n) -> ∞` and strictly
  increasing sizes.
- `A_n ⊆ G` are images of the `X_n` under maps that are isometric for the word metric, with `d(A_n, A_m) -> ∞`.
- `x_n = 1_(A_n)`, `Ŷ = closure(∪_n G·x_n)`, `U = ∪_n G·x_n`, `∂Y = Ŷ \ U`.
- For a finitely supported `m : G \ S_pat -> Z`, put `b_m = Σ_([s]) m_([s]) [1_(C_s ∩ ∂Y)]` in
  `K_0(C_0(∂Y \ {0}) ⋊_r G)`, and `L_m(B) = Σ_(t <= 1_B) m_([t])` for finite `B ⊆ G`.

Here `1 ∈ Λ \ {0}` is a fixed symbol, and `x_n = 1_(A_n)` takes the value `1` on `A_n` and `0` elsewhere.

**Lemma 1.1** (items 1 and 2 of the 2026-09-13 artifact, reproved here so that nothing below depends on that artifact).
Assume (M), and put `N_n = {v ∈ G : d(v, A_n) <= 1}`.
- (a) If `z ∈ X \ {0}` is the limit of `g_i x_(n_i)` and `n_i` does not tend to `∞`, then `z ∈ U`.
- (b) Each `x_n` has trivial stabilizer.
- (c) If `z ∈ Ŷ` agrees with `x_n` on `N_n`, then `z = x_n`. So each `x_n` is isolated in `Ŷ`, `U` is open in `Ŷ`, and
  `∂Y` is closed and invariant in `X`.
- (d) `C_0(U) ≅ c_0(N × G)` equivariantly, and `0 -> C_0(U) -> C_0(Ŷ \ {0}) -> C_0(∂Y \ {0}) -> 0` is exact.

*Proof.*
- **(a).**
  - Pass to a subsequence with `n_i = n` constant. Pick `h ∈ supp z`.
  - The topology is pointwise, so `h ∈ g_i A_n` for large `i`. Then `g_i ∈ h A_n^(-1)`, a finite set.
  - Pass to a further subsequence with `g_i = g` constant. Then `z = g x_n ∈ U`.
- **(b).** If `g A_n = A_n`, then `g` permutes the finite set `A_n`, so `g^k` fixes a point for `k = |A_n|!`. Hence
  `g^k = e`, and `g = e` because `G` is torsion-free.
- **Connectedness.** An edge of `X_n` goes to a pair at word distance `1`, that is, to an edge of `Cay(G, S)`. So the
  subgraph of `Cay(G, S)` induced on each translate `g A_m` is connected.
- **A claim.** If `g A_m ⊇ A_n` and `g A_m ∩ (N_n \ A_n) = ∅`, then `g A_m = A_n`, `m = n` and `g = e`.
  - Suppose `v ∈ g A_m \ A_n`. Take a path from a point of `A_n` to `v` in the induced subgraph on `g A_m`.
  - Its first vertex outside `A_n` is adjacent to `A_n`, so it lies in `N_n \ A_n`, a contradiction.
  - So `g A_m = A_n`. Then `|A_m| = |A_n|`, so `m = n` because the sizes strictly increase, and `g = e` by (b).
- **(c).**
  - If `z = g x_m ∈ U`, agreement on `N_n` says `g A_m ⊇ A_n` and `g A_m ∩ (N_n \ A_n) = ∅`. By the claim, `z = x_n`.
  - Otherwise `z ∈ Ŷ \ U`, and `z ≠ 0` because `z = 1` on `A_n`. `X` is metrizable and `U` is dense in `Ŷ`, so
    `z = lim g_i x_(n_i)`, and `n_i -> ∞` by (a).
  - `N_n` is finite, so for large `i` the configuration `g_i x_(n_i)` agrees with `x_n` on `N_n`. The claim gives
    `n_i = n`, which contradicts `n_i -> ∞`.
  - Hence `{z ∈ Ŷ : z|_(N_n) = x_n|_(N_n)}` is the open singleton `{x_n}` of `Ŷ`. Translation is a homeomorphism, so
    every point of `U` is isolated in `Ŷ`. So `U` is open, and `∂Y = Ŷ \ U` is closed and invariant.
- **(d).**
  - `U` is the disjoint union of the orbits `G·x_n`, which are distinct because the sizes `|A_n|` differ. Each orbit is
    a discrete open subset of `Ŷ`, equivariantly homeomorphic to `G` by (b). This gives `C_0(U) ≅ c_0(N × G)`.
  - `U` is open in `Ŷ \ {0}` with closed complement `∂Y \ {0}`. That gives the exact sequence. QED.

**Consequence used below.** If `y ∈ ∂Y \ {0}` is the limit of `g_i x_(n_i)`, then `n_i -> ∞`, by (a).

## 2. The imported dual-Dirac statement

BGW, *Expanders, exact crossed products, and the Baum-Connes conjecture*, arXiv:1311.2343v3, extracted text read
2026-09-16.

**Definition 6.1 (BGW, adapted from Tu, Section 3).** An action of `G` on a locally compact space `X` (written on the
right) is **a-T-menable** if there is a continuous `h : X × G -> R` such that:
1. `h(x, e) = 0` for all `x`;
2. `h(x, g) = h(xg, g^(-1))` for all `x, g`;
3. `Σ_(i,j) t_i t_j h(x g_i, g_i^(-1) g_j) <= 0` for all `x ∈ X`, `g_1, ..., g_n ∈ G` and real `t_i` with `Σ t_i = 0`;
4. (**locally proper**) for every compact `K ⊆ X`, the restriction of `h` to `{(x, g) : x ∈ K, xg ∈ K}` is proper.

**Imported consequence** (claim `a-t-menable-actions-have-tu-dual-dirac-elements`). If a countable discrete `G` acts
a-T-menably on a second countable locally compact `X`, there are a proper `X ⋊ G`-algebra `A` and
`α ∈ KK^G(A, C_0(X))`, `β ∈ KK^G(C_0(X), A)` with `β ⊗_A α = 1` in `KK^G(C_0(X), C_0(X))`. For proper `A`, all crossed
products agree and assembly is an isomorphism.

The quotes, and the caveat that Tu's own paper was not fetched, are in the citation route.

## 3. Theorem A: CND-support shifts are a-T-menable

**Lemma 3.1.** `T_cnd` is closed, `G`-invariant and hereditary: if `x ∈ T_cnd` and `supp x' ⊆ supp x`, then
`x' ∈ T_cnd`. It contains `0` and every configuration with at most one support point.

*Proof.*
- **Hereditary** and the last sentence are immediate from the definition.
- **Invariant.** `supp(g·x) = g supp x`, and `d(g u, g v) = d(u, v)`, so `d` restricted to `gF` is CND iff it is on `F`.
- **Closed.** Let `x_k -> x` with `x_k ∈ T_cnd`, and let `F ⊆ supp x` be finite. The topology is pointwise and `Λ` is
  finite, so `x_k|_F = x|_F` for large `k`. Then `F ⊆ supp x_k`, so `d` restricted to `F` is CND. QED.

**Theorem A.** Let `Z ⊆ T_cnd^0` be closed in `X^0` and `G`-invariant. The action `x g = g^(-1)·x` of `G` on `Z` is
a-T-menable in the sense of BGW Definition 6.1.

*Proof.*
1. **A continuous basepoint.**
   - Enumerate `G = {h_1, h_2, ...}` and put `U_k = {x ∈ X : x(h_k) ≠ 0 and x(h_j) = 0 for j < k}`.
   - Each `U_k` is clopen in `X`. They are pairwise disjoint, and their union is `X^0`.
   - Define `a_0 : X^0 -> G` by `a_0 = h_k` on `U_k`. It is locally constant, and `a_0(x) ∈ supp x`.
2. **The function.** For `x ∈ Z` and `g ∈ G` put

   ```text
   h(x, g) = d( g^(-1) a_0(x), a_0(xg) ).
   ```

   For fixed `g`, `x ↦ xg` is continuous and `a_0` is locally constant. So `h` is locally constant on `Z × G`, hence
   continuous.
3. **Condition 1.** `h(x, e) = d(a_0(x), a_0(x)) = 0`.
4. **Condition 2.** `h(xg, g^(-1)) = d(g a_0(xg), a_0(x))`. By left invariance this is `d(a_0(xg), g^(-1) a_0(x))`,
   which is `h(x, g)`.
5. **Condition 3.**
   - Fix `x ∈ Z`, `g_1, ..., g_n` and `t_i` with `Σ t_i = 0`. Then

     ```text
     h(x g_i, g_i^(-1) g_j) = d( g_j^(-1) g_i a_0(x g_i), a_0(x g_j) ) = d(p_i, p_j),   p_i := g_i a_0(x g_i).
     ```

     The second equality multiplies both arguments on the left by `g_j`.
   - Since `a_0(x g_i) ∈ supp(x g_i) = g_i^(-1) supp x`, every `p_i` lies in `supp x`.
   - `d` restricted to the finite set `{p_1, ..., p_n} ⊆ supp x` is CND because `x ∈ T_cnd`. So
     `Σ t_i t_j h(x g_i, g_i^(-1) g_j) = Σ t_i t_j d(p_i, p_j) <= 0`.
6. **Condition 4 (local properness).**
   - Let `K ⊆ Z` be compact. `K` is covered by the open sets `U_k`, so `K ⊆ U_1 ∪ ... ∪ U_m` for some `m`. Then
     `a_0(K) ⊆ F := {h_1, ..., h_m}`. Put `M = max_(f ∈ F) |f|`.
   - For `x ∈ K` and `xg ∈ K`, with `a = a_0(x)` and `b = a_0(xg)`, the triangle inequality gives
     `h(x, g) = d(g^(-1) a, b) >= d(g^(-1), e) - d(g^(-1) a, g^(-1)) - d(b, e) = |g| - |a| - |b| >= |g| - 2M`.
   - So for `R >= 0`, `{(x, g) : x ∈ K, xg ∈ K, h(x, g) <= R}` lies in `K × {g : |g| <= R + 2M}`. That set is compact,
     because balls in `G` are finite.
   - The set on the left is closed, since `h` and `x ↦ xg` are continuous. So it is compact, and `h` restricted to
     `{x ∈ K, xg ∈ K}` is proper. QED.

**Remarks.**
- `Z` is second countable and locally compact: it is closed in the open subset `X^0` of the compact metrizable `X`.
- No hypothesis on `G` is used beyond finite generation. The hypothesis on supports is used only in Condition 3, and
  only for distances between points of a single support.
- **Model tests.**
  - If `d` is CND on all of `G`, then `T_cnd = X`. Examples are `Z^k` with the standard generators (the `ℓ^1` metric)
    and free groups with a free basis (tree metric).
  - There Theorem A says the whole Bernoulli action on `X^0` is a-T-menable. This is consistent with Higson--Kasparov
    for these a-T-menable groups.
  - Every metric on at most four points embeds isometrically in `ℓ^1`, so every configuration with at most four support
    points lies in `T_cnd`. This fact is standard and used only in this remark.
- **Why the forest shift is different.** `forest-shift-bernoulli-comparison-is-surjective` records that the forest
  shift `T` is not a-T-menable in general: two far-apart forest components realize the pair groupoid. The obstruction
  is the *word* metric between components. `T_cnd` asks for CND of the word metric on the whole support, components
  included, so it does not contain those configurations unless their metric is CND. `T` and `T_cnd` are incomparable in
  general.

## 4. Theorem B: Baum--Connes and K-amenability over CND-support shifts

**Theorem B.** Let `G` be finitely generated and `Z ⊆ T_cnd^0` closed in `X^0` and `G`-invariant. Then, in both
degrees:
- (a) `mu_r : K^top_*(G; C_0(Z)) -> K_*(C_0(Z) ⋊_r G)` is an isomorphism;
- (b) `mu_max : K^top_*(G; C_0(Z)) -> K_*(C_0(Z) ⋊_max G)` is an isomorphism;
- (c) `(λ_Z)_* : K_*(C_0(Z) ⋊_max G) -> K_*(C_0(Z) ⋊_r G)` is an isomorphism.

*Proof.*
1. **Dual-Dirac elements.**
   - By Theorem A and the imported claim, there are a proper `Z ⋊ G`-algebra `A`, `α ∈ KK^G(A, C_0(Z))` and
     `β ∈ KK^G(C_0(Z), A)` with `β ⊗_A α = 1`.
   - For proper `A`, `mu_(r, A)` is an isomorphism (`bernoulli-shift-weak-k-equivalence-and-going-down`, item 3; BGW
     cite Chabert--Echterhoff--Meyer [11, Théorème 2.2]).
   - `(λ_A)_*` is an isomorphism, because all crossed products of a proper algebra agree (BGW, proof of Theorem 6.2).
   - Since `mu_(r, A) = (λ_A)_* ∘ mu_(max, A)`, `mu_(max, A)` is an isomorphism as well.
2. **Functoriality.** Write `x_* = K^top(x)` on the topological side and `j(x)_*` for the Kasparov product with the
   descended element on the crossed-product side, for either crossed product.
   - Functoriality of descent and of `K^top` for Kasparov products gives `α_* β_* = id` and `j(α)_* j(β)_* = id` on the
     groups for `C_0(Z)`.
   - Naturality of assembly gives `mu_Z ∘ α_* = j(α)_* ∘ mu_A` and `mu_A ∘ β_* = j(β)_* ∘ mu_Z`.
3. **(a) and (b), surjectivity.** For `v ∈ K_*(C_0(Z) ⋊ G)`, with `⋊` either crossed product:

   ```text
   v = j(α)_* j(β)_* v = j(α)_* mu_A( mu_A^(-1) j(β)_* v ) = mu_Z( α_* mu_A^(-1) j(β)_* v ).
   ```

4. **(a) and (b), injectivity.** If `mu_Z(u) = 0`, then `mu_A(β_* u) = j(β)_* mu_Z(u) = 0`. So `β_* u = 0`, and
   `u = α_* β_* u = 0`.
5. **(c).** `mu_(r, Z) = (λ_Z)_* ∘ mu_(max, Z)`, and both assembly maps are isomorphisms by (a) and (b). So
   `(λ_Z)_* = mu_(r, Z) ∘ mu_(max, Z)^(-1)` is an isomorphism. QED.

**Remark.**
- Step 5 needs no compatibility of `λ` with descent, only the factorization of reduced assembly through maximal
  assembly.
- For (b), BGW Theorem 6.2 at the maximal crossed product would be an alternative. It needs the maximal crossed product
  to be exact and Morita compatible. BGW state Morita compatibility ("Both the maximal and reduced crossed product
  functors are Morita compatible: see Lemma A.6 in the appendix"). The exactness line was not located in the extracted
  text, so the argument above does not use Theorem 6.2.

## 5. Theorem C: the tree boundary lies in the CND-support shift

**Lemma 5.1 (balls in large girth).** Let `Γ` be a simple connected graph with path metric `d_Γ`, and `R >= 0`.
- (i) If `girth(Γ) > 2R + 1`, the subgraph induced on the ball `B(v, R)` is a tree, for every vertex `v`.
- (ii) If `F` is a vertex set with `diam_Γ(F) <= r` and `girth(Γ) > 4r + 1`, then `d_Γ` restricted to `F` is the
  restriction of the path metric of a tree. In particular it is CND.

*Proof.*
- **(i).**
  - Let `T` be a breadth-first spanning tree of the induced subgraph on `B(v, R)`, rooted at `v`, so every tree path
    from `v` has length at most `R`.
  - Suppose some edge `uw` of the induced subgraph is not in `T`. Let `m` be the last common vertex of the tree paths
    `v -> u` and `v -> w`.
  - The tree paths `m -> u` and `m -> w`, together with `uw`, form a cycle. It has at least three edges: if `m = u`,
    the tree path `u -> w` has length at least `2`, since `uw` is not a tree edge. Its length is at most `2R + 1`.
  - That contradicts the girth, so the induced subgraph equals `T`.
- **(ii).**
  - Fix `f_0 ∈ F` and put `B = B(f_0, 2r)`. By (i) with `R = 2r`, the induced subgraph on `B` is a tree `T`.
  - For `u, w ∈ F`, a `Γ`-geodesic from `u` to `w` has length at most `r`, and each of its vertices is within `2r` of
    `f_0`. So it is a path in `T`, and `d_T(u, w) <= d_Γ(u, w)`. Also `d_Γ <= d_T`, so `d_Γ = d_T` on `F`.
  - Tree metrics are CND (Haagerup). Concretely, orient each edge `ε` of `T` away from `f_0` and let `h_ε` be the set of
    vertices on its far side. For `ξ_u = Σ_ε 1_(h_ε)(u) δ_ε ∈ ℓ^2(edges)`, `d_T(u, w) = ||ξ_u - ξ_w||^2`, because the
    edges separating `u` from `w` are exactly those with `1_(h_ε)(u) ≠ 1_(h_ε)(w)`. A kernel of the form
    `||ξ_u - ξ_w||^2` is CND. QED.

**Theorem C.** Assume (M). Then `∂Y \ {0} ⊆ T_cnd^0`, and `∂Y \ {0}` is closed in `X^0` and `G`-invariant. So Theorem B
applies to `Z = ∂Y \ {0}`. In particular

```text
K_*(C_0(∂Y \ {0}) ⋊_max G) -> K_*(C_0(∂Y \ {0}) ⋊_r G)
```

is an isomorphism in both degrees, which gives (H-K). Also `mu_(G, C_0(∂Y \ {0}))` is an isomorphism.

*Proof.*
- **Closed and invariant.** `U` is open in the closed invariant set `Ŷ` (Lemma 1.1), so `∂Y` is closed and invariant in
  `X`, and `∂Y \ {0}` is closed in `X^0`.
- **CND supports.**
  - Let `y ∈ ∂Y \ {0}`. `X` is metrizable, so `y = lim g_i x_(n_i)` for a sequence in `U`, and `n_i -> ∞` by Lemma 1.1.
  - `g_i x_(n_i) = 1_(g_i A_(n_i))`. Let `F ⊆ supp y` be finite with `diam_d(F) = r`. As in Lemma 3.1, `F ⊆ g_i A_(n_i)`
    for all large `i`.
  - Choose `i` so large that also `girth(X_(n_i)) > 4r + 1`.
  - `g_i^(-1) F ⊆ A_(n_i)`, and `d` restricted to `A_(n_i)` is the path metric of `X_(n_i)` transported by an isometry.
    By Lemma 5.1(ii), `d` restricted to `g_i^(-1) F` is CND, hence so is `d` restricted to `F`.
- **Conclusion.** Apply Theorem B(c). QED.

**Remarks.**
- This settles the stopping point recorded in `expander-tree-boundary-k0-max-reduced-injective`. No nearest-point
  projection is needed: the basepoint `a_0` of Theorem A is an arbitrary locally constant choice of a support point,
  and all the geometry enters through CND of the word metric on single supports.
- `x_n ∉ T_cnd` for large `n`.
  - If `d` restricted to `A_n` were CND, then by Schoenberg there would be `ξ : A_n -> ℓ^2` with
    `||ξ_u - ξ_w||^2 = d(u, w)`.
  - The Poincaré inequality of the spectral gap gives
    `Σ_(u,w) ||ξ_u - ξ_w||^2 <= (2|A_n| / ε) Σ_(edges uw) ||ξ_u - ξ_w||^2 = D |A_n|^2 / ε`.
  - Here `ε` is the least nonzero eigenvalue of the combinatorial Laplacian; another normalization changes the constant
    by a factor `D`.
  - So the average distance in `X_n` would be at most `D / ε`. It tends to infinity for `D`-regular graphs of growing
    size.
  - Hence `Ŷ ⊄ T_cnd`, as it must be: HLS non-exactness lives on `Ŷ`.

## 6. Theorem D: the HLS class never lifts to the full shift

Throughout this section `G` is finitely generated and torsion-free, and `H := T_cnd`. Put
`S_H = {s ∈ S_pat : x_s ∈ H}`, the patterns whose support carries a CND word metric. `S_H` is `G`-invariant. For
`s ∈ S_H`, every sub-pattern of `x_s` is in `S_H`.

**Lemma 6.1 (hereditary basis).**
- (i) For a pattern `s`, `C_s ∩ H ≠ ∅` iff `s ∈ S_H`.
- (ii) The classes `[1_(C_s ∩ H)]`, `s ∈ S_H`, form a `Z`-basis of `K_0(C_0(H \ {0})) = C_c(H \ {0}, Z)`, and
  `K_1(C_0(H \ {0})) = 0`.
- (iii) `Θ_H : c_0(S_H) -> K(ℓ^2 S_H) ⊗ C_0(H \ {0})`, `δ_s ↦ e_ss ⊗ 1_(C_s ∩ H)`, is a `G`-equivariant
  *-homomorphism, with `G` acting on `K(ℓ^2 S_H)` through the permutation representation. It is a weak K-equivalence.
- (iv) `K^top_*(G; C_0(H \ {0})) ≅ ⊕_(G \ S_H) Z` in degree `0` and `0` in degree `1`. The image of
  `mu_(G, C_0(H \ {0}))` is the image of

  ```text
  T_r^H : ⊕_(G \ S_H) Z -> K_0(C_0(H \ {0}) ⋊_r G),   [s] ↦ [1_(C_s ∩ H)].
  ```

*Proof.*
- **(i).** If `s ∈ S_H`, then `x_s ∈ C_s ∩ H`. If `y ∈ C_s ∩ H`, then `F_s ⊆ supp y`, and hereditarity gives
  `x_s ∈ H`.
- **(ii), spanning.**
  - `H \ {0}` is totally disconnected, locally compact and second countable. So `K_1 = 0`, `K_0` is `C_c(H \ {0}, Z)`,
    and `K_0` is spanned by indicators of compact open sets `V ⊆ H \ {0}`.
  - `V = W ∩ H` with `W` open in `X^0`. Cover `V` by finitely many compact open cylinders of `X^0` contained in `W`, and
    let `V'` be their union. Then `V'` is compact open in `X^0` and `V' ∩ H = V`.
  - By CC item 4, the `1_(C_s)` form a `Z`-basis of `C_c(X^0, Z)`. So `1_(V') = Σ c_s 1_(C_s)`, and restricting to `H`
    gives `1_V = Σ c_s 1_(C_s ∩ H)`. By (i), the terms with `s ∉ S_H` vanish.
- **(ii), independence.**
  - Suppose `Σ_(s ∈ S_H) c_s 1_(C_s ∩ H) = 0`, a finite sum with some `c_s ≠ 0`. Pick `s'` with `c_(s') ≠ 0` and
    `|F_(s')|` minimal, and evaluate at `x_(s') ∈ H`.
  - `x_(s') ∈ C_s` iff `F_s ⊆ F_(s')` and `a_s = x_(s')|_(F_s)`. Among the `s` with `c_s ≠ 0` this forces `s = s'`, by
    minimality. So `c_(s') = 0`, a contradiction.
- **(iii).**
  - The `e_ss` are orthogonal, so `Θ_H` is a *-homomorphism, and `g·(e_ss ⊗ 1_(C_s ∩ H)) = e_(gs,gs) ⊗ 1_(C_(gs) ∩ H)`.
  - `G` is torsion-free, so the only finite subgroup is trivial, and weak K-equivalence means that `Θ_H` induces
    isomorphisms on `K_*`. By (ii) it does: `K_0(c_0(S_H)) = ⊕_(S_H) Z` maps basis to basis, and both `K_1` vanish.
- **(iv).**
  - Going-down (`bernoulli-shift-weak-k-equivalence-and-going-down`, item 2) gives
    `K^top_*(G; c_0(S_H)) ≅ K^top_*(G; C_0(H \ {0}))`.
  - Pattern stabilizers are finite, hence trivial, so `c_0(S_H) ≅ ⊕_([s]) c_0(G)` is proper. By item 3, `mu` is an
    isomorphism onto `K_0(c_0(S_H) ⋊_r G) = ⊕_([s]) Z`, generated by the rank-one classes `[δ_s]`.
  - Naturality of assembly (`amenable-kernel-bc-transfer-and-ktop-half-exactness`, item 3) and the untwisting
    isomorphism `(K(ℓ^2 S_H) ⊗ B) ⋊_r G ≅ K(ℓ^2 S_H) ⊗ (B ⋊_r G)` send `[δ_s]` to `[1_(C_s ∩ H)]`. This is exactly
    the argument of CC item 4, with `X^0` replaced by `H \ {0}`. QED.

**Corollary 6.2 (= Corollary E).** For every finitely generated torsion-free `G`, `T_r^H` is an isomorphism and
`K_1(C_0(T_cnd \ {0}) ⋊_r G) = 0`.

*Proof.* `mu_(G, C_0(H \ {0}))` is an isomorphism by Theorem B(a), since `H \ {0}` is closed in `X^0` and invariant
(Lemma 3.1). Combine with Lemma 6.1(iv). QED.

**Lemma 6.3 (ranks factor through restriction).** Let `W ⊆ X` be closed and invariant, and `res_W :
C_0(X^0) ⋊_r G -> C_0(W \ {0}) ⋊_r G` the restriction. For a pattern `x ∈ W`, `π_x = π_x^W ∘ res_W`, where `π_x^W` is
the orbit representation of `C_0(W \ {0}) ⋊_r G`. Hence `r_x = K_0(π_x^W) ∘ (res_W)_*`, and
`K_0(π_x^W)[1_(C_s ∩ W)] = r_x[1_(C_s)] = #{t <= x : t ∈ G s}`.

*Proof.*
- `π_x^W` is the regular representation induced from evaluation at `x`, so it is defined on the reduced crossed
  product.
- The two sides agree on the dense algebraic crossed product, because the orbit `G·x` lies in `W`.
- The rank formula is RF Lemma R2, applied through `res_W(1_(C_s)) = 1_(C_s ∩ W)`. QED.

**Proposition 6.4 (key step without (H-K)).** Assume (M). Let `m : G \ S_H -> Z` be finitely supported with `b_m = 0`.
Then `L_m(A_n) = 0` for all large `n`.

*Proof.*
1. **A topological preimage.**
   - Put `Ŷ^0 = Ŷ \ {0}` and `w = Σ_([s]) m_([s]) [1_(C_s ∩ Ŷ)] ∈ K_0(C_0(Ŷ^0) ⋊_r G)`.
   - As in Lemma 6.1(iv), `Θ_Ŷ : c_0(S_H) -> K(ℓ^2 S_H) ⊗ C_0(Ŷ^0)`, `δ_s ↦ e_ss ⊗ 1_(C_s ∩ Ŷ)`, is an equivariant
     *-homomorphism, and `c_0(S_H)` is proper.
   - So `ξ := K^top(Θ_Ŷ)( mu_(c_0(S_H))^(-1)(m) ) ∈ K^top_0(G; C_0(Ŷ^0))` satisfies `mu_Ŷ(ξ) = w`, by naturality.
2. **Its boundary part vanishes.**
   - Let `q : C_0(Ŷ^0) -> C_0(∂Y \ {0})` be restriction. Naturality gives `mu_∂(q_* ξ) = q_* w = b_m = 0`.
   - By Theorem C, `mu_∂ = mu_(G, C_0(∂Y \ {0}))` is injective, so `q_* ξ = 0`.
3. **Half-exactness.**
   - `0 -> C_0(U) -> C_0(Ŷ^0) -> C_0(∂Y \ {0}) -> 0` is exact, since `U` is open in `Ŷ^0` (Lemma 1.1).
   - Half-exactness of `K^top` (`amenable-kernel-bc-transfer-and-ktop-half-exactness`, item 3) gives
     `κ ∈ K^top_0(G; C_0(U))` with `ι_* κ = ξ`.
   - Then `w = ι_*( mu_U(κ) )`.
4. **Counting.**
   - `C_0(U) ⋊_r G ≅ ⊕_n c_0(G·x_n) ⋊_r G ≅ c_0(N, K(ℓ^2 G))`. So `k := mu_U(κ)` lies in `K_0 = ⊕_n Z` and has finite
     support.
   - The orbit representation `π_(x_n)` kills the summands `m ≠ n` and is the standard isomorphism
     `c_0(G·x_n) ⋊ G ≅ K(ℓ^2 G)` on the summand `n`. So `r_(x_n)(w) = k_n`, which is `0` for large `n`.
   - On the other hand, Lemma 6.3 with `W = Ŷ` gives `r_(x_n)(w) = Σ_([s]) m_([s]) #{t <= x_n : t ∈ G s} = L_m(A_n)`.
   QED.

**Theorem D.** Let `Λ` be any finite alphabet with `0 ∈ Λ` (for instance `Z/p`), and let `G` satisfy (M). Let
`y ∈ K_0(C_0(X^0) ⋊_r G)` have `y|_(∂Y) = 0`. Then `r_(x_n)(y) = 0` for all but finitely many `n`.

In particular no prime `p` and host `G` satisfying (M), with or without (H-K), carry a class as in
`hls-ghost-class-lifts-to-the-bernoulli-full-shift`. The HLS class `[p]` has no lift along
`C_0(X^0) ⋊_r G -> C_0(Ŷ^0) ⋊_r G`, since a lift would have `y|_(∂Y) = q_*[p] = 0` and `r_(x_n)(y) = 1` for all `n`.

*Proof.*
1. **Restriction to `H`.** Let `res_H : C_0(X^0) ⋊_r G -> C_0(H \ {0}) ⋊_r G`. By Corollary 6.2 there is a finitely
   supported `m' : G \ S_H -> Z` with `res_H(y) = T_r^H(m')`.
2. **Identification of `m'`.**
   - For a pattern `x ∈ H`, Lemma 6.3 and the rank formula give `r_x(y) = Σ_(t <= x) m'_([t])`. Every `t <= x` lies in
     `S_H`, by hereditarity.
   - The pattern expansion satisfies `r_x(y) = Σ_(t <= x) n_([t])(y)` (RF item 3).
   - Möbius inversion on the Boolean lattice of subsets of `supp x` (RF Lemma R5) determines the coefficients from the
     ranks, by induction on `|supp x|`. So `n_([x])(y) = m'_([x])` for every pattern `x ∈ S_H`.
3. **The boundary identity.**
   - `∂Y \ {0} ⊆ H \ {0}` by Theorem C, so restriction to `∂Y` factors through `res_H`.
   - `y|_(∂Y) = Σ_([s] ⊆ S_H) m'_([s]) [1_(C_s ∩ ∂Y)] = b_(m')`. So `b_(m') = 0`, and Proposition 6.4 gives
     `L_(m')(A_n) = 0` for all large `n`.
4. **Locality.**
   - By LOC Corollary 2 there is `d_0 = d_0(y)` with `n_([t])(y) = 0` whenever `diam supp t >= d_0`. Also
     `r_x(y) = Σ_(t <= x) n_([t])(y)` for every finite-support `x`.
   - Take `n` so large that `girth(X_n) > 4 d_0 + 1` and `L_(m')(A_n) = 0`. Compare the two sums
     `r_(x_n)(y) = Σ_(t <= x_n) n_([t])(y)` and `L_(m')(A_n) = Σ_(t <= x_n) m'_([t])`, where `m'` is `0` off `S_H`.
     Term by term, for `t <= x_n`:
     - if `diam supp t < d_0`, then `supp t ⊆ A_n` has diameter below `d_0`. By Lemma 5.1(ii) and the isometry,
       `d` restricted to `supp t` is CND, so `t ∈ S_H` and `n_([t])(y) = m'_([t])`;
     - if `diam supp t >= d_0` and `t ∈ S_H`, both terms are `n_([t])(y) = 0`;
     - if `diam supp t >= d_0` and `t ∉ S_H`, both terms are `0`.
   - Hence `r_(x_n)(y) = L_(m')(A_n) = 0`. QED.

**Scope of Theorem D.**
- The alphabet is arbitrary and (H-K) is not assumed. (H-K) is true anyway by Theorem C.
- The hypothesis "`r_(x_n)(y) ≠ 0` for infinitely many `n`" is never satisfiable. So the theorem of
  `hls-ghost-lift-needs-forest-shift-failure` (Theorem G of the 2026-09-13 artifact) is vacuous.
- (F) (`forest-shift-bernoulli-comparison-is-surjective`) is not decided. Its role in deciding the HLS lift is taken
  over by Corollary 6.2 on `T_cnd`.

## 7. What changes and where it stops

**Graph consequences.**
- `expander-tree-boundary-k0-max-reduced-injective` is established, by Theorem C.
- `hls-ghost-class-lifts-to-the-bernoulli-full-shift` is refuted, by Theorem D. So route
  `bc-bernoulli-defect-via-hls-ghost-lift` is invalidated, and `bernoulli-cylinder-comparison-fails-for-some-group` has
  no live route.

**What a Bernoulli witness must now look like.** Let `G` be torsion-free and finitely generated, and `y ∉ im T_r`. By
Corollary 6.2 and step 2 of Theorem D, `y - T_r(n(y))` restricts to `0` on `T_cnd`. So a witness is invisible to:
- every orbit representation at a finite pattern (RF, LOC: shape (b));
- restriction to any closed invariant set of configurations with CND supports, in particular to every tree-like
  boundary.

It has to be carried by configurations whose supports contain finite sets with non-CND word metric, and not through
the ranks at those sets either. The HLS mechanism is ranks on marked expanders certified by the boundary, and it
fails for exactly this reason.

**Where the HLS picture goes instead.**
- HLS non-exactness at `0 -> C_0(U) -> C_0(Ŷ^0) -> C_0(∂Y \ {0}) -> 0` concerns the subshift `Ŷ`, not the full shift.
- The ghost projection lives over `Ŷ` and restricts to `0` on `∂Y`.
- Theorem D shows that no full-shift class maps onto it. Whatever the full-shift K-theory of a monster is, it does not
  see `[p]`.
- This is consistent with `mu_(G, C_0(X^0))` being surjective, but does not prove it.

**Open follow-ups.**
- (i) Is `mu_(G, C_0(X^0))` surjective for a monster host? By CC and LOC this is shape (b) or (c).
- (ii) A class supported on non-CND supports: `y` with `res_(T_cnd) y = 0` and `y ∉ im T_r`. Reduced crossed products
  are not exact, so `y` need not come from `C_0(X^0 \ T_cnd) ⋊_r G`.
- (iii) Theorems A and B extend verbatim to any countable `G` with a proper left-invariant metric `d` in place of the
  word metric, and to `Z = G/K` with `K` finite. This is not written.

## 8. Checks

- **Model tests.**
  - `G = Z` and `G = F_k` with free bases: `T_cnd = X` and Theorem B recovers Baum--Connes at the Bernoulli coefficient,
    consistent with Pimsner--Voiculescu and Higson--Kasparov.
  - `Z^2` with standard generators: the `ℓ^1` metric is CND, so `T_cnd = X`, consistent.
  - For a monster host, `x_n ∉ T_cnd` for large `n` (Section 5) while `∂Y \ {0} ⊆ T_cnd`, consistent with HLS: the
    failure sits on `Ŷ`.
- **Consistency with Finn-Sell.** Finn-Sell (arXiv:1401.6841v2, Theorem 4.3 and Corollary 4.4) proves a-T-menability for
  the boundary groupoid `Ω_(∂βX) ⋊ Γ` of the coarse picture. Theorem C is the analogous statement for the
  transformation groupoid of the tree-boundary subshift. No map between the two spaces is used.
- **Bounded novelty check** (2026-09-16).
  - Read: BGW arXiv:1311.2343v3, Sections 2, 4, 6, 7; Finn-Sell arXiv:1304.3348v4, Section 3 (Definition 14 and the Tu
    equivalence); Finn-Sell arXiv:1401.6841v2, Section 4; Willett--Yu arXiv:1012.4150v1, which does not use Tu.
  - Searched the graph: `a-T-menable`, `CND`, `forest`, `tree boundary`.
  - The CND-support shift and the refutation of the lift were not found. The web-search budget of this session was
    exhausted, so the check is bounded.
