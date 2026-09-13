# Left-orderability of lattices in products of trees (part 2): specialization, drift tuning, the Poisson boundary gap

Lane z1-22-lo-simple-bm, 2026-09-13. Continues `zp-tree-lattice-left-orderability-2026-09-13.md` (part 1).
Serves `irreducible-tree-product-lattices-are-not-left-orderable`. Unreviewed working notes.

## 1. Specialization to Burger–Mozes simple lattices

Let `Λ = π_1(X) < U(F_1) × U(F_2)` be a Burger–Mozes lattice with `F_i` 2-transitive and dense
projections (`burger-mozes-infinitely-transitive-tree-groups`, item 5). Let `Γ ≤ Λ` be its simple
subgroup of finite index.

- `Γ ≤ U(F_1)^+ × U(F_2)^+`. `U(F_i)^+` has index 2 in `U(F_i)` (item 4), so `Γ ∩ (U^+ × U^+)` has
  finite index in `Γ`, and a simple infinite group has no proper finite-index subgroup.
- The projection of `Γ` to `U(F_i)^+` is dense. Its closure `C_i` is open of finite index in `U(F_i)`,
  because it contains a finite-index subgroup of the dense projection of `Λ`. So `C_i` contains
  `U(F_i)^(∞) = U(F_i)^+` (item 4). It is also contained in `U(F_i)^+`.
- So take `G_i = U(F_i)^+`. This group is closed, simple (item 4), locally `∞`-transitive, hence
  2-transitive on `∂T_i` (item 1). It acts on the `d_i`-regular tree preserving the bipartition, so
  `T_i` is bi-regular of valence `d_i ≥ 3` for this action.
- `Γ` is perfect, being simple and non-abelian, and torsion-free.

**Consequences.**

- **(G7) settled.** `tree-product-lattice-circle-actions-have-fixed-points` applies.
- **(G3) available.** Item 3 of `howe-moore-property-for-simple-lie-and-p-adic-groups` (reviewed import
  of Ciobotaru, arXiv:1403.0223, Theorem 1.1) gives Howe–Moore for `G_i`.
  - `G_1` acts ergodically on `G/Γ`. A `G_1`-invariant function is a function on `G_2/π_2(Γ)`, and a
    dense subgroup of `G_2` acts ergodically on `G_2` by translation.
  - So every hyperbolic `a_1 ∈ G_1` acts mixingly, hence ergodically, on `G/Γ`, and so does
    `(a_1, 1)`.
  - For interior elements `(a_1, a_2)` use `product-of-tree-groups-has-factorwise-howe-moore`
    (unreviewed), or Howe–Moore for each factor plus the absence of factor-invariant vectors in
    `L^2_0(G/Γ)`.
- **Open big cell (part 1, step 9).** For a half-tree fixator in `U(F)` to act transitively on the
  ends of the complementary half-tree, one needs Tits' independence property of `U(F)` and
  2-transitivity of `F`. Half-tree fixators fix an edge, so they lie in `U(F)^+`. So the argument runs
  inside `G_i = U(F_i)^+`.

## 2. (G5) drift direction inside the discrete group `A`

Witte Morris, Corollary 3.48 (p. 16), needs `â_P ∈ W_P ∖ {1}` with
`ℓ_O(g_n ⋯ g_1 k â_P^(-n)) / n → 0` for `μ_G^∞`-a.e. sequence. Here `A = ⟨α_1, α_2⟩ ≅ Z^2` is discrete.

- **Choice of measure.** Take `μ_G = μ_1 ⊗ μ_2` with `μ_i` bi-`K_i`-invariant, compactly supported,
  absolutely continuous, symmetric, with `K_i ⊆ supp μ_i`, which makes the walk aperiodic.
- **The walk.** `x_n = g_1^(-1) ⋯ g_n^(-1) o` has independent coordinates `x_n^i`, which are
  space-homogeneous random walks on `V(T_i)`. Since `K_i` is transitive on spheres, the transition
  law from a vertex depends only on distance: the walk is isotropic.
- **Drift.** Isotropic walks on a bi-regular tree of valence `≥ 3` are transient. They converge to an
  end `η_i` along a geodesic ray with linear rate `ℓ_i > 0`: `d(x_n^i, o_i) = n ℓ_i + o(n)`, and
  `d(x_n^i, [o_i, η_i)) = o(n)`.
- **Tuning.** `ℓ_i` depends continuously on the weights `μ_i(K_i h K_i)` of the finitely many double
  cosets in the support, and it is non-constant in them. So the weights can be chosen with
  `ℓ_i / t_i ∈ Q`, where `t_i` is the translation length of `a_i`. Replacing `μ_G` by a convolution
  power `μ_G^(*N)` multiplies both drifts by `N`, so `ℓ_1 = p t_1` and `ℓ_2 = q t_2` with positive
  integers `p`, `q`. Put `â_P = α_1^p α_2^q`.
- **Tracking.** Choose `k = (k_1, k_2) ∈ K` with `k_i ξ_i^- = η_i`, using (F1) of part 1. Then
  `k â_P^(-n) o` lies at distance `o(n)` from `x_n`. By Švarc–Milnor for the proper cocompact action of
  `G` on the vertices of `T_1 × T_2`, word length is at most a constant times displacement plus a
  constant, so `ℓ_O(g_n ⋯ g_1 k â_P^(-n)) = o(n)`.
  - Uniformity of `k` follows from `K`-invariance of `μ_G`.
  - Proposition 3.49 (independence of `â_P` from the sequence) holds because the drifts are
    deterministic.
- **Still to check.** The exposition's measures must also satisfy "support of `μ_Γ` generates `Γ`"
  (Definition 3.13, or Definition 5.4 when `G ≠ KΓ`). Enlarging the support by more double cosets keeps
  the tuning argument, since the drift stays continuous in the weights.

## 3. (G4) Furstenberg's decomposition: the remaining structural input

**Needed.** For `μ_G` as in §2 and every compact metrizable `G`-space `X`, every `μ_G`-stationary
probability `ν` on `X` is `∫_K k_* λ dm_K` for a unique `P`-invariant `λ`, where
`P = G_(1,ξ_1) × G_(2,ξ_2)`. This is Witte Morris, Theorem 3.28, citing Furstenberg.

**Plan.**

1. **Martingale limit.** `β(ω) = lim_n (g_1 ⋯ g_n)_* ν` exists a.s. and `ν = E[β]` (Furstenberg).
2. **Reduction to the chain.** By Witte Morris Lemma 5.2, bounded `μ_G`-harmonic functions are left
   `K`-invariant. So the Poisson boundary of `(G, μ_G)` is the Poisson boundary of the chain of §2 on
   `V(T_1) × V(T_2)`.
3. **Each factor.** The Poisson boundary of an isotropic finite-range random walk on a bi-regular tree
   is `∂T_i` with the hitting distribution, which here is the unique `K_i`-invariant measure. To import:
   Cartier's theorem and its finite-range extensions in Woess's monograph; exact statements not yet read.
4. **Product.** For the product measure `μ_1 ⊗ μ_2`, the Poisson boundary is
   `∂T_1 × ∂T_2`. To import: the product lemma used by Bader–Shalom for the factor theorem, or Kaimanovich's
   ray criterion. Exact statements not yet read.
5. **Conclusion.** Given 3 and 4, `β` factors a.s. through the limit end pair `η ∈ ∂T_1 × ∂T_2 = G/P`,
   giving a measurable equivariant `β : G/P → Prob(X)`. `λ = β(eP)` is `P`-invariant, and
   `ν = ∫_K k_* λ dm_K`.
   - Uniqueness: if `λ'` also works, then `kP ↦ k_* λ'` is an equivariant map with the same barycenter,
     and it agrees with the martingale limit along a.e. path, because `(G/P, ν_B)` is a `μ_G`-boundary.
     So `λ' = λ`.

Recorded as open claim `tree-product-stationary-measures-are-parabolic-averages`.
