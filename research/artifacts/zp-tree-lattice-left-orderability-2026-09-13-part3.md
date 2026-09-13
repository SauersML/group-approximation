# Left-orderability of lattices in products of trees (part 3): Furstenberg's decomposition for products of tree groups

Lane z1-22-lo-simple-bm, 2026-09-13. Proves `tree-product-stationary-measures-are-parabolic-averages`
(gap G4 of parts 1–2). Unreviewed.

## 0. Setting and imports

`G = G_1 × G_2` with `G_i ≤ Aut(T_i)` closed, non-compact, 2-transitive on `∂T_i`, and `T_i` locally
finite. `K = K_1 × K_2` is the stabilizer of `o = (o_1, o_2)`. `B = ∂T_1 × ∂T_2 = G/P` for
`P = G_(1,ξ_1) × G_(2,ξ_2)`. Here `μ_G` is bi-`K`-invariant, compactly supported, absolutely continuous and
symmetric, and its support generates `G`. `Γ ≤ G` is a cocompact lattice, torsion-free and finitely
generated, with `μ_Γ` as in Witte Morris §5.

Imports:

- **(K)** V. A. Kaimanovich, *The Poisson formula for groups with hyperbolic properties*, Ann. of Math.
  152 (2000), arXiv:math/9802132v2, **Theorem 6.5** (p. 677), read from the PDF:
  > Suppose that 𝒢 is a subadditive temperate gauge on a countable group G ... and μ is a probability
  > measure on G. Let (B_−, λ_−) and (B_+, λ_+) be μ̌- and μ-boundaries, respectively, and there exists a
  > measurable G-equivariant map B_− × B_+ ∋ (b_−, b_+) ↦ S(b_−, b_+) ⊂ G. If either (a) the measure μ has
  > a finite first moment Σ|g|μ(g), and for λ_− ⊗ λ_+-a.e. (b_−, b_+), (1/k) log card[S(b_−,b_+) ∩ 𝒢_k] → 0
  > ... then the boundaries (B_−, λ_−) and (B_+, λ_+) are maximal.
- **(WM5)** D. Witte Morris, arXiv:2407.09742v1, §5 (pp. 25–28).
  - Lemma 5.2: every `μ_G`-harmonic function is left `K`-invariant.
  - Remark 5.3: a harmonic function on `G` is determined by its values on `Γ`, by optional stopping at
    the hitting time of `KΓ`.
  - Lemma 5.5: `μ_Γ` has an exponential tail in word length.
  - Proposition 5.6: bounded `μ_Γ`-harmonic functions extend uniquely to `μ_G`-harmonic functions.
- **(Kes)** Statement-level, classical: a symmetric spread-out probability measure on a non-amenable
  locally compact second countable group has spectral radius `< 1` on `L^2`. Derriennic–Guivarc'h,
  Berg–Christensen; not re-read here.

## 1. The walk converges to `B`, with the `K`-invariant hitting measure

Let `x_n = g_1 ⋯ g_n` with `g_j` i.i.d. `μ_G`, and `x_n^i` the coordinates of `x_n o`.

1. `G_i` is non-amenable. A non-compact boundary-2-transitive `G_i` contains a hyperbolic element `a`.
   `a` moves the unique `K_i`-invariant probability measure on `∂T_i` (it contracts toward its attracting
   end), so `G_i` preserves no probability measure on the compact space `∂T_i`. An amenable group acting
   continuously on a compact space would preserve one.
2. By (Kes) the transition operator of the chain `x_n o` on vertices, which is `G`-invariant and
   symmetric, has spectral radius `ρ < 1`. So `P[x_n^i = v] ≤ C ρ^n` uniformly in `v`.
3. The balls of radius `cn` in `T_i` have at most `D^(cn)` vertices, where `D` is the maximal valence. For
   `c` small, `Σ_n D^(cn) ρ^n < ∞`, so by Borel–Cantelli `d(o_i, x_n^i) ≥ cn` for all large `n`, almost
   surely.
4. The increments are bounded, since `d(x_n o, x_(n+1) o) = d(o, g_(n+1) o) ≤ R` by compact support.
   So the Gromov products satisfy `(x_n^i | x_(n+1)^i)_(o_i) ≥ cn − R → ∞`, and `x_n^i` converges to an
   end `η_i`.
5. The law `ν_B` of `η = (η_1, η_2)` is `K`-invariant, because `μ_G` is left `K`-invariant. `K_i` is
   transitive on `∂T_i` (part 1, F1), so `ν_B` is the unique `K`-invariant probability on `B`. It is
   nonatomic in each coordinate and `μ_G`-stationary.
6. `(B, ν_B)` is a `μ_G`-boundary, i.e. an equivariant quotient of path space:
   `η(ω) = g_1 η(Tω)`.

The same holds for `μ̌_G = μ_G`.

## 2. `(B, ν_B)` is the Poisson boundary of `(Γ, μ_Γ)`

- **Γ-walk.** Sampling the `G`-walk at its successive hitting times of `KΓ` gives the `μ_Γ`-walk on `Γ`
  (WM5, Definition 5.4). It has the same limit point. So `(B, ν_B)` with this limit map is a
  `μ_Γ`-boundary. The analogous statement for the reversed walk gives a `μ̌_Γ`-boundary `(B, ν_B^-)` with
  nonatomic coordinates.
- **Moment.** `μ_Γ` has finite first moment by WM5 Lemma 5.5.
- **Strips.** For `b_± = (η_1^±, η_2^±)` with `η_i^- ≠ η_i^+`, which holds `ν_B^- ⊗ ν_B`-a.e. by
  nonatomicity, let `ℓ_i` be the geodesic line from `η_i^-` to `η_i^+`, so `F = ℓ_1 × ℓ_2` is a flat. Put
  `S(b_-, b_+) = {γ ∈ Γ : d(γ o, F) ≤ M}`, with `M` larger than the diameter of a fundamental domain for
  the vertex action. Then `S` is nonempty and measurable, and `S(γ b_-, γ b_+) = γ S(b_-, b_+)`.
- **Growth.** `Γ` acts freely on vertices. Word length is at least `d(o, γ o)/L` for some `L` (Švarc–Milnor).
  So `card[S ∩ 𝒢_k]` is at most the number of vertices of `T_1 × T_2` within `M` of `F` and within `Lk`
  of `o`, which is `≤ C_M (Lk + M)^2`. So `(1/k) log card[S ∩ 𝒢_k] → 0`.
- **Conclusion.** By (K), Theorem 6.5(a), `(B, ν_B)` is the Poisson boundary of `(Γ, μ_Γ)`.

## 3. Bounded `μ_G`-harmonic functions are Poisson integrals over `B`

Let `f` be bounded and `μ_G`-harmonic on `G`.

- By Remark 5.3 its restriction to `Γ` is `μ_Γ`-harmonic. By §2 there is `F ∈ L^∞(B, ν_B)` with
  `f(γ) = ∫_B F(γ b) dν_B(b)` for `γ ∈ Γ`.
- The function `h(g) = ∫_B F(g b) dν_B(b)` is `μ_G`-harmonic, because `ν_B` is `μ_G`-stationary, and it
  agrees with `f` on `Γ`.
- By uniqueness in WM5 (Remark 5.3, Proposition 5.6), `f = h`.

## 4. Existence and uniqueness of the decomposition

Let `X` be a compact metrizable `G`-space and `ν` a `μ_G`-stationary probability on `X`.

- **Existence.**
  - For `φ ∈ C(X)` the function `g ↦ ∫ φ d(g_* ν)` is bounded and `μ_G`-harmonic. By §3 it equals
    `∫_B F_φ(g b) dν_B(b)` for a unique `F_φ ∈ L^∞(B)`, which is linear and positive in `φ`, with
    `F_1 = 1`.
  - Separability of `C(X)` gives a measurable `β : B → Prob(X)` with `∫ φ dβ(b) = F_φ(b)` a.e. It is
    `G`-equivariant a.e. and `∫_B β dν_B = ν`.
  - `G` acts transitively on `B = G/P`, so `β` agrees a.e. with a strictly equivariant map. This is the
    standard lemma on measurable equivariant maps from a transitive space (Zimmer, *Ergodic theory and
    semisimple groups*, §B; statement-level import).
  - `λ := β(eP)` is `P`-invariant. By `G = KP`, `ν = ∫_B β dν_B = ∫_K β(kP) dm_K(k) = ∫_K k_* λ dm_K`.
- **Uniqueness.**
  - Let `λ'` be `P`-invariant with `∫_K k_* λ' dm_K = ν`. Then `β'(kP) = k_* λ'` is well defined, strictly
    equivariant, and `∫_B β' dν_B = ν`.
  - Along a.e. path, `η(ω) = x_n η(T^n ω)` with `T^n ω` independent of `ℱ_n` and distributed like `ω`.
    So `E[β'(η(ω)) | ℱ_n] = ∫_B β'(x_n b) dν_B(b) = (x_n)_* ν`.
  - By martingale convergence, `β'(η(ω)) = lim_n (x_n)_* ν` a.s. The same holds for `β`. So `β = β'`
    `ν_B`-a.e., hence everywhere by strict equivariance and transitivity, and `λ' = β'(eP) = β(eP) = λ`.

This is Witte Morris Theorem 3.28 for `G = G_1 × G_2`. Uniqueness used only §1. Existence used §§1–3,
hence a cocompact lattice `Γ`, which the Deroin–Hurtado argument has anyway.

## 5. Trust surface

- (Kes) and the measurable-selection lemma are statement-level imports, not re-read.
- WM5 is an expository sketch. Proposition 5.6 is proved there for bounded `f`, which is the case used.
- (K) was read verbatim. The gauge is the word gauge of the finitely generated `Γ`.
