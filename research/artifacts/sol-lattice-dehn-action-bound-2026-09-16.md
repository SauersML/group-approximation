# Sol lattices satisfy the Dehn action bound for every action in (S)

Swarm lane on `zaremsky-1-17-dehn-function-from-cocompact-action-data`,
2026-09-16. This is the full proof behind
`sol-lattice-actions-satisfy-the-dehn-action-bound` (route
`sol-lattice-dehn-action-bound-proof`). It is a calibration of the open claim
`some-action-violates-dehn-bound-without-finite-index-faces`: no Sol lattice
is a counterexample, whatever complex it acts on. It does not settle the root.

## 0. Statement and conventions

**Setting (S)**, as in the root claim. `G` acts cellularly, cocompactly and
without inversions on a simply connected simplicial complex `X` with
`δ_X(n) < ∞`. Vertex stabilizers are finitely presented and edge stabilizers
finitely generated. Write

```text
dist_X(n) = max { dist^G_{G_σ}(n) : σ a cell of X, dim σ ≤ 2 },
R_X(n)    = δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) ),
```

where `f‾` is the superadditive closure. (UB) is the assertion `δ_G ≼ R_X`.

**Definitions used**, from Llosa Isenrich–Weis, arXiv:2608.07191v1
(7 August 2026), §2.1, read on 2026-09-16:

- `f ≼ g` means `f(n) ≤ C g(Cn + C) + Cn + C` for some `C > 0`.
- `dist^G_H(n) = max { ℓ_H(h) : h ∈ H, ℓ_G(h) ≤ n }`.
- `δ_X(n) = max { FVol_X(γ) : Vol_X(γ) ≤ n }` over admissible loops `γ`
  (Definition 2.3). `FVol_X(γ)` is the minimum, over admissible maps
  `φ : D² → X` with `φ|∂D² = γ`, of `Vol_X(φ)`: the number of open 2-cells of
  `D²` that `φ` maps homeomorphically onto open 2-cells of `X`. "Admissible"
  means singular combinatorial for some combinatorial cell structure on the
  disc: each open cell maps homeomorphically onto an open cell of the same
  dimension, or into the skeleton of one dimension lower (Definition 2.2).

**Normalization (N).** Every Dehn function (`δ_G`, `δ_X`, `δ_{G_v}`) is
replaced by `max{δ(n), n}`, and `dist_X(n)` by `max{dist_X(n), n}`.

Some normalization of this kind is forced if (UB), or Theorems B and C of
Llosa Isenrich–Weis, are to be non-degenerate:

- **Dehn functions.** `ℤ² = ⟨a, t | [t, a]⟩` is an HNN extension of `ℤ`, and
  `δ` of the presentation `⟨a | ⟩` is `0`. Read literally, Theorem B would give
  `δ_{ℤ²} ≼ 0`.
- **Distortion.** For a free cocompact action, every stabilizer is trivial, so
  `dist_X ≡ 0` and `R_X(n) = δ_X(n) · δ_1(0) = 0`, while `δ_G ≃ δ_X`.

In §3.1 of the paper the area estimates have the form
`max_v δ_{G_v}(n + edist_X(Dn))`, which is what (N) encodes. We use (N) only
in two places. Cases 0 and 1 use `δ(m) ≥ m`. Case 2 uses only
`δ_{G_v}(dist_X‾(δ_X(n))) ≥ 1` for `n ≥ 1`.

Dehn functions and `dist_X` are nondecreasing. `f‾ ≥ f`, and `f‾` is
nondecreasing when `f ≥ 0`, since `f‾(n+1) ≥ f‾(n) + f(1)`.

**Theorem.** Let `M ∈ GL_2(ℤ)` be hyperbolic, i.e. without eigenvalues of
modulus 1, and let `G = ℤ² ⋊_M ℤ = ⟨a, b, t | [a, b], t a t⁻¹ = M(a),
t b t⁻¹ = M(b)⟩`. Under (N), every action of `G` in setting (S) satisfies
`δ_G ≼ R_X`. In fact `R_X(n) ≽ δ_G(n)`, and `R_X(n) ≽ e^n` in Cases 1 and 2
below.

## 1. Algebra of M

Let `τ = tr M` and `d = det M = ±1`, so `χ(x) = x² − τx + d`.

- **Hyperbolic.** For `d = 1` this means `|τ| > 2`; for `d = −1` it means
  `τ ≠ 0`.
- **Irreducible.** The discriminant `τ² − 4d` is not a perfect square. For
  `d = 1`, `τ² − 4 = k²` forces `|τ| = 2`; for `d = −1`, `τ² + 4 = k²` forces
  `τ = 0`. So `χ` is irreducible over `ℚ`, and its roots `λ, λ'` are real
  irrational quadratic units with `λλ' = d` and `|λ| > 1 > |λ'| = |λ|⁻¹`.
- **Powers.** For `k ≠ 0`, `λ^k` is irrational. If `λ^k` were rational it
  would be a rational algebraic integer, hence in `ℤ`, and so would
  `λ'^k = d^k/λ^k`, forcing `λ^k = ±1`. Hence `M^k` has no rational
  eigenvector, and in particular no eigenvalue `1`: `det(M^k − I) ≠ 0`.
- **Ring map.** Put `ℤ[λ] = ℤ + ℤλ ⊂ ℝ`. The map `p(λ) ↦ p(M)` is a
  well-defined ring homomorphism `ℤ[λ] → M_2(ℤ)` by Cayley–Hamilton. It sends
  `λ⁻¹ = d(τ − λ)` to `d(τI − M) = M⁻¹`.

**Affine action.** Let `G` act on `ℝ²` by `t·p = Mp` and `y·p = p + y` for
`y ∈ ℤ²`. This is a homomorphism, because
`t y t⁻¹ · p = M(M⁻¹p + y) = p + My`. Every `g ∈ G` acts as `p ↦ L_g p + c_g`
with `L_g ∈ ⟨M⟩`, so `det L_g = ±1`, and `c_g = g·0`.

**Fixed points.** An element `h = w t^k` with `w ∈ ℤ²` and `k ≠ 0` acts as
`p ↦ M^k p + w`. It has exactly one fixed point, `(I − M^k)⁻¹ w`. All nonzero
powers of `h` have unique fixed points, and each of them fixes the fixed point
of `h`, so they all have the same one.

## 2. Lemma 1: `δ_G ≼ e^n`

For `x ∈ {a^{±1}, b^{±1}}` and `ε = ±1`, fix a word `μ_ε(x)` in `a^{±1}, b^{±1}`
representing `t^{−ε} x t^{ε} = M^{−ε}x`. Let `K ≥ 2` bound their lengths and
`C_0` bound the areas of the finitely many relations `x t^ε = t^ε μ_ε(x)`.
Extend `μ_ε` letterwise to fiber words.

Let `w` be a null-homotopic word of length `n`, written
`w = u_0 t^{ε_1} u_1 ⋯ t^{ε_k} u_k` with fiber words `u_i` and `k ≤ n`. Put
`v_0 = u_0`, and for `j = 1, …, k` rewrite `v_{j−1} t^{ε_j}` as
`t^{ε_j} μ_{ε_j}(v_{j−1})` and set `v_j = μ_{ε_j}(v_{j−1}) u_j`.

- **Lengths.** Inductively `|v_j| ≤ K^j n`.
- **Cost.** Step `j` costs at most `C_0 K^{j−1} n`, so the total is at most
  `C_0 n² K^n`.
- **Result.** The word becomes `t^{ε_1} ⋯ t^{ε_k} v_k`. The exponent sum of `t`
  in `w` is `0`, because `w` maps to `0` in `G/ℤ² ≅ ℤ`, so the `t`-prefix
  freely reduces to the empty word.
- **Finish.** `v_k` represents `1`, i.e. the zero vector of `ℤ²`, and has
  length `m ≤ nK^n`. A null-homotopic word of length `m` in `⟨a, b | [a, b]⟩`
  has area at most `m²`: sorting the letters needs at most `m²` commutations.

Hence `Area(w) ≤ C_0 n² K^n + n² K^{2n}`, and `δ_G(n) ≤ C_1^n` for some `C_1`
and all `n ≥ 1`. (That `δ_G ≃ e^n` is classical, but only this upper bound is
used.)

## 3. Lemma 2: subgroups meeting the fiber

If `H ≤ G` and `H ∩ ℤ² ≠ 0`, then `H ≤ ℤ²` or `[G : H] < ∞`.

*Proof.* Take `0 ≠ y ∈ H ∩ ℤ²` and suppose `h = w t^k ∈ H` with `k ≠ 0`.
Then `h y h⁻¹ = M^k y ∈ H ∩ ℤ²`. By §1, `y` is not an eigenvector of `M^k`,
so `y` and `M^k y` are linearly independent, and `H ∩ ℤ²` has finite index in
`ℤ²`. The image of `H` in `G/ℤ² ≅ ℤ` contains `kℤ`. Hence
`[G : H] ≤ [ℤ² : H ∩ ℤ²] · |k| < ∞`. ∎

## 4. Lemma 3: logarithmic fiber distortion

For `0 ≠ z ∈ ℤ²` there is `C` with `ℓ_G(z^m) ≤ C log(|m| + 2)` for all
`m ∈ ℤ`.

*Proof.* Put `B = ⌈|λ|/2⌉ + 1`. Embed `ℤ[λ]` in `ℝ²` by `ι(p) = (p, p')`,
where `'` is Galois conjugation. `ι(ℤ[λ]) = ℤ ι(1) + ℤ ι(λ)` is a lattice,
since `λ ≠ λ'`, so every bounded box meets it in finitely many points.

1. **Positive powers.** Let `K ≥ 0` be minimal with `|m| ≤ |λ|^K / 2`. For
   `j = K, K−1, …, 0`, put `c_j = round(x/λ^j)` and replace `x` by
   `x − c_j λ^j`, starting from `x = m`. Before step `j`,
   `|x| ≤ |λ|^{j+1}/2`, so `|c_j| ≤ B`; after it, `|x| ≤ |λ|^j/2`. Hence
   `r_1 = m − Σ_{j=0}^K c_j λ^j ∈ ℤ[λ]` has `|r_1| ≤ 1/2`, and its conjugate
   satisfies `|r_1'| ≤ |m| + B/(1 − |λ'|)`.
2. **Negative powers.** The conjugate of `λ^{−j}` is `λ'^{−j}`, of modulus
   `|λ|^j`. Run the same greedy rounding on `y = r_1'` with the numbers
   `λ'^{−j}` for `j = K', …, 1`, where `K'` is minimal with
   `|r_1'| ≤ |λ|^{K'}/2`. This gives digits `|d_j| ≤ B`. The element
   `s = r_1 − Σ_{j=1}^{K'} d_j λ^{−j} ∈ ℤ[λ]` then satisfies
   `|s'| ≤ |λ|/2` and `|s| ≤ 1/2 + B/(|λ| − 1)`.
3. **Finite remainder set.** So `ι(s)` lies in a fixed box, and `s` ranges over
   a finite set `S ⊂ ℤ[λ]` independent of `m`. Also `K, K' ≤ C log(|m| + 2)`.
4. **Back to matrices.** Applying the ring map of §1 to
   `m = Σ c_j λ^j + Σ d_j λ^{−j} + s` gives
   `m z = Σ_{j=0}^K c_j M^j z + Σ_{j=1}^{K'} d_j M^{−j} z + s(M) z`.
5. **Words.** `Σ_{j=0}^K c_j M^j z` is represented by the Horner word
   `z^{c_0} t z^{c_1} t z^{c_2} ⋯ t z^{c_K} t^{−K}`. This is the product of the
   `t^j z^{c_j} t^{−j}` after cancellation, and it has length
   `≤ 2K + (K + 1) B ℓ_G(z)`. The same holds for the negative part with `t⁻¹`.
   `s(M) z` ranges over a finite set of vectors. ∎

## 5. Lemma 4: area transfer

Suppose `G` acts on `ℝ²` by affine maps whose linear parts have determinant
`±1`, and let `f : X^(0) → ℝ²` be `G`-equivariant.

- **1-chains.** For an oriented edge `e = (x, y)` put
  `A(e) = ½ det(f(x), f(y))`. This is antisymmetric in the orientation, so it
  extends linearly to the cellular chains `C_1(X)`.
- **Edge paths.** For an edge path `x_0, …, x_r`,
  `A = ½ Σ det(f(x_{i−1}), f(x_i))`: the shoelace sum of the polygon
  `f(x_0), …, f(x_r)`.
- **Triangles.** For an oriented 2-simplex `σ = [x_0, x_1, x_2]`, `A(∂σ)` is
  the signed area of the triangle `f(x_0) f(x_1) f(x_2)`. Since `f(gσ) = g·f(σ)`
  and `g` is affine with `|det L_g| = 1`, `|A(∂σ)|` is constant on `G`-orbits.
  Put `C_X = max |A(∂σ)|` over the finitely many orbits of 2-simplices.

**Claim.** For every admissible `φ : D² → X` whose boundary is an edge loop
`γ`, `|A(γ)| ≤ C_X · Vol_X(φ)`. Hence `FVol_X(γ) ≥ |A(γ)| / C_X` whenever
`A(γ) ≠ 0`, and then `C_X > 0`.

*Proof.* A singular combinatorial map is cellular, since each open `n`-cell
goes into `X^(n)`, so it induces a chain map `φ_*` on cellular chains.

- **2-cells.** A 2-cell of `D²` mapped homeomorphically onto a 2-simplex `σ`
  contributes `±σ`. A singular 2-cell lies in `X^(1)` and contributes `0`.
- **Pushforward.** So `c = φ_*[D²] = Σ n_σ σ` with `Σ |n_σ| ≤ Vol_X(φ)`, and
  `∂c = φ_*(∂[D²]) = [γ]`. Singular boundary 1-cells map to vertices, and they
  contribute `det(p, p) = 0` to `A` anyway.
- **Estimate.** `A(γ) = A(∂c) = Σ n_σ A(∂σ)`, so
  `|A(γ)| ≤ C_X Σ |n_σ|`. ∎

## 6. Lemma 5: comparison with orbit polygons

Fix a vertex `x_0` and put `p_0 = f(x_0)`. For `s ∈ {a, b, t}`, fix an edge
path `β_s` from `x_0` to `s x_0`, and put
`β_{s⁻¹} = reverse(s⁻¹ β_s)`, a path from `x_0` to `s⁻¹x_0`. Let `L` bound
the lengths `|β_s|`.

For a word `w = σ_1 ⋯ σ_m` with `w = 1` in `G`, let `g_i = σ_1 ⋯ σ_i`, and let
`γ_w` be the concatenation of the translated paths `g_{i−1} β_{σ_i}`. This is
an edge loop at `x_0` of length `≤ Lm`. Let `P_w` be the closed polygon
`g_0 p_0, g_1 p_0, …, g_m p_0 = p_0`, with shoelace area
`sh(P_w) = ½ Σ det(g_{i−1}p_0, g_i p_0)`.

**Claim.** `|A(γ_w) − sh(P_w)| ≤ C' m`, where `C'` depends only on the `β_s`
and `f`.

*Proof.* Let `Q_σ` be the closed polygon made of `f(β_σ)` followed by the
segment from `σ p_0` back to `p_0`. Then `g_{i−1} Q_{σ_i}` is `f(g_{i−1}β_{σ_i})`
closed by the segment `g_i p_0 → g_{i−1} p_0`, by equivariance. Hence

```text
A(γ_w) − sh(P_w) = Σ_i A(g_{i−1} Q_{σ_i}).
```

The shoelace area of a closed polygon is invariant under translation and is
multiplied by `det T` under a linear map `T`. So
`|A(g Q_σ)| = |A(Q_σ)|`. Also `Q_{s⁻¹}` is the reverse of `s⁻¹ Q_s`. So
`C' = max_s |A(Q_s)|` works. ∎

## 7. Lemma 6: the commutator polygon

Let `u = M^n e_1` and `v = M^{−n} e_1`, and let
`w_n = [t^n a t^{−n}, t^{−n} a t^n]`, a word of length `8n + 4` equal to `1`
in `G`. For the affine action of §1 and **every** `p_0 ∈ ℝ²`,

```text
sh(P_{w_n}) = det(u, v) = d^n αβ det(ξ, η) (λ^{2n} − λ^{−2n}),
```

where `e_1 = αξ + βη` with `Mξ = λξ` and `Mη = λ'η`. Here `αβ ≠ 0` because
`e_1` is not an eigenvector.

*Proof.* Write `c_i = c_{g_i}`, `L_i = L_{g_i}`, and `q_i = L_i p_0`, so that
`g_i p_0 = c_i + q_i`. Bilinearity splits `sh(P_{w_n})` into
`T_1 + T_2 + T_3`:

- `T_1 = ½ Σ det(c_{i−1}, c_i)`,
- `T_2 = ½ Σ [det(c_{i−1}, q_i) + det(q_{i−1}, c_i)]`,
- `T_3 = ½ Σ det(q_{i−1}, q_i)`.

At a `t^{±1}`-step, `c_i = c_{i−1}` and `L_i = L_{i−1} M^{±1}`. At an
`a^{±1}`-step, `L_i = L_{i−1}` and `Δc_i = ±L_{i−1} e_1`.

- **`T_1`.** `c` changes only at the four `a`-letters. It runs
  `0 → u → u + v → v → 0`, with `L_{i−1} = M^n, M^{−n}, M^n, M^{−n}` at those
  letters. So `T_1` is the shoelace area of that parallelogram,
  `½[det(u, u+v) + det(u+v, v)] = det(u, v)`.
- **`T_3`.** At `a`-steps `q_i = q_{i−1}`, so those terms vanish. The
  exponents `k_i` with `L_i = M^{k_i}` form a closed walk on `ℤ`. With
  `D = det(p_0, Mp_0)`, an up-step `k → k+1` contributes `½ d^k D`, and a
  down-step `k+1 → k` contributes `½ det(M^{k+1}p_0, M^k p_0) = −½ d^k D`. A
  closed walk crosses each `{k, k+1}` equally often in both directions, so
  `T_3 = 0`.
- **`T_2`.** `det(c_{i−1}, q_i) + det(q_{i−1}, c_i)
  = det(c_{i−1}, Δq_i) + det(q_{i−1}, Δc_i)`. Summation by parts over the
  closed sequence (`c_0 = c_m = 0`) gives
  `Σ det(c_{i−1}, Δq_i) = −Σ det(Δc_i, q_i) = Σ det(q_i, Δc_i)`. Since
  `Δc_i ≠ 0` only where `q_i = q_{i−1}`,
  `T_2 = Σ_{a-steps} det(q_{i−1}, Δc_i) = det(p_0, e_1) Σ_{a-steps} ± det L_{i−1}`.
  The signs are `+, +, −, −` and `det L_{i−1} = d^n` each time, so `T_2 = 0`.
- **Eigen-expansion.** `M^{±n} e_1 = αλ^{±n}ξ + βλ'^{±n}η` gives
  `det(u, v) = αβ det(ξ, η)((λ/λ')^n − (λ'/λ)^n)`, and `λ/λ' = dλ²`. ∎

## 8. Proof of the theorem

Fix an action in (S). Let `R = R_X` under (N), and let `x` range over vertices.
Lemma 2 gives exactly three cases.

**Case 0: some `G_x` has finite index.** `G_x` is finitely presented and
quasi-isometric to `G`, so `δ_{G_x} ≃ δ_G`. This is the classical
quasi-isometry invariance of Dehn functions (J. M. Alonso, *Inégalités
isopérimétriques et quasi-isométries*, C. R. Acad. Sci. Paris Sér. I 311
(1990); the repo already relies on the same paper in
`cocompact-action-data-do-not-determine-dehn-function`). It was not re-read
this session. For a finite-index subgroup it is the elementary comparison of
two free cocompact actions on the same Cayley 2-complex. Under (N), `δ_X(n) ≥ n ≥ 1` and
`dist_X‾(δ_X(n)) ≥ dist_X(n) ≥ n`. So `R(n) ≥ δ_{G_x}(n) ≽ δ_G(n)`.

**Case 1: some `G_x` is a nontrivial subgroup of `ℤ²`.** Pick
`0 ≠ z ∈ G_x`. `G_x ≅ ℤ` or `ℤ²`, cyclic subgroups of free abelian groups are
undistorted, so `ℓ_{G_x}(z^m) ≥ c|m|`. By Lemma 3,
`ℓ_G(z^m) ≤ C log(|m| + 2)`. Taking `m = ⌊e^{r/C}⌋ − 2` gives
`dist^G_{G_x}(r) ≥ c(e^{r/C} − 3)`. Under (N),

```text
R(n) ≥ δ_{G_x}(dist_X‾(δ_X(n))) ≥ dist_X‾(δ_X(n)) ≥ dist_X(n) ≥ c(e^{n/C} − 3).
```

With Lemma 1 this gives `R ≽ e^n ≽ δ_G`.

**Case 2: otherwise.** By Lemma 2, `G_x ∩ ℤ² = 0` for every vertex `x`, so
`G_x` embeds in `G/ℤ² ≅ ℤ`. Hence `G_x` is trivial or generated by some
`w t^k` with `k ≠ 0`.

- **Equivariant map.** By §1, a nontrivial `G_x` has a unique common fixed
  point `f(x)`. Uniqueness gives `f(gx) = g f(x)` for all `g`, since
  `G_{gx} = g G_x g⁻¹`. On each of the finitely many orbits with trivial
  stabilizer, choose `f` at one representative and extend equivariantly. So
  `f : X^(0) → ℝ²` is equivariant for the area-preserving affine action of §1.
- **Transfer.** Lemmas 4, 5 and 6 applied to `w_n` give

  ```text
  δ_X(L(8n + 4)) ≥ FVol_X(γ_{w_n}) ≥ ( |det(u, v)| − C'(8n + 4) ) / C_X
                 ≥ c_1 |λ|^{2n} − C_2 n − C_2.
  ```

  (Lemma 6 makes `A(γ_{w_n}) ≠ 0` for large `n`, so `C_X > 0`.)
- **Conclusion.** So `δ_X(N) ≥ e^{N/C_3} − C_3` for all `N`. Under (N),
  `dist_X‾(δ_X(N)) ≥ N ≥ 1`, so `δ_{G_x}(…) ≥ 1` and `R(N) ≥ δ_X(N)`. With
  Lemma 1, `δ_G ≼ e^N ≼ R`. ∎

## 9. Remarks and scope

1. **What this rules out.** The calibration concerns the upper-bound reading
   of Zaremsky 1.17. A Sol lattice has exponential Dehn function. Every action
   in (S) shows that exponential somewhere in the data: in `δ_{G_x}` (Case 0),
   in `dist_X` (Case 1: a fiber element in a stabilizer), or in `δ_X` itself
   (Case 2: the invariant area form survives, because the stabilizers fix
   points). No action of `ℤ² ⋊_M ℤ` can be a counterexample to
   (UB), including actions on 2-complexes with infinite-index face stabilizers
   and uncontrolled twists.
2. **General principle behind Case 2.** Suppose `G` acts on `ℝ²` by
   area-preserving affine maps such that every vertex stabilizer has a fixed
   point. Then `δ_X(n)` dominates the orbit-polygon area function
   `max { |sh(P_w)| : |w| ≤ n, w = 1 } − O(n)`. This is a lower bound for
   `δ_X`, not an upper bound for `δ_G`.
3. **Where the argument does not reach.** For the Heisenberg group `H_3` with
   vertex stabilizers cyclic and non-central, the stabilizers act on the
   abelianization plane by translations with no fixed points, and Case 2 has no
   analogue. There (UB) needs `δ_X ≽ n^{3/2}`, which is not proved; see
   `notes/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16.md`.
4. **Computation.**
   `experiments/zaremsky-1-17-dehn-function-from-cocompa-swarm-2026-09-16/sol_orbit_polygon_area.py`
   (output in `sol_orbit_polygon_area.out`, "ALL CHECKS PASSED") checks three
   things:
   - Lemma 6 in exact rational arithmetic, for `M = [[2,1],[1,1]]`,
     `[[1,1],[1,0]]` (determinant `−1`) and `[[3,2],[1,1]]`, with `n ≤ 10` and
     three random rational base points each;
   - `det(M^k − I) ≠ 0` for `1 ≤ |k| ≤ 30`;
   - a floating-point sanity check of the digit expansion in Lemma 3, with
     bounded digits and residuals and word length `/ log m` stable for
     `m ≤ 10¹²`.

   The proof does not depend on the script.
