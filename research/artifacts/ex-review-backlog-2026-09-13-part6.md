# EX review, backlog, part 6: refill lanes, second batch (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`. Read at tips `b3083ac22` to `4a2087802`.

## 17. ex-hyperbolic-triangle-search (2adae648cf, 2cf32255b1, e26c4c06ee): the a7a7a8 representation exclusions: PASS on method, certificates not re-run

The claims are `a7a7a8-triangle-candidates-no-small-linear-representation` and
`a7a7a8-triangle-candidates-no-4dim-char2-representation`. Both compute established through `requires: []` routes,
and both say "computer-assisted and unreviewed".

**These are elimination certificates, not searches.**
- Every nontrivial representation is vertex-injective.
- The vertex modules are classified.
- The torus parametrisation covers every representation up to conjugacy.
- A Gröbner basis `[1]` for necessary trace equations excludes all of them over the algebraic closure.
- So if the code computes the stated ideals, the exclusions are exhaustive.

**Module lists, re-derived.**
- A faithful representation of a simple group has a nontrivial composition factor, because a unipotent image
  is a `p`-group.
- `A_8` has no nontrivial irreducible of degree `<= 6` in characteristic `0`, `3`, `5`, or coprime to `|A_8|`. So
  its faithful `7`-dimensional module is the heart `7`.
- For `A_7`, `7 = 1 + 6`.
  - `H^1(A_7, F_p^7) = H^1(A_6, F_p) = 0` by Shapiro, since `A_6` is perfect. So `H^1(A_7, 6) = 0`, and the
    module is forced to be `1 ⊕ 6`.
  - Characteristics `11, 13, 29, 43` are coprime to `|A_8|`.
- In characteristic `2`, a faithful `4`-dimensional module of `A_7 < A_8 ≅ SL_4(2)` has composition factors among
  `1, 4, 4*`, hence is `4` or `4*`.

**Distinct eigenvalues.** An element of order `7` has seven distinct eigenvalues on `1 ⊕ 6` and on the heart `7`,
and four on `4`. So its centralizer is a torus.

**Not checked.**
- The eigenvalue sign identity `σ(G)` for `G_2` and `G_4`.
- The 117 trace words.
- The Singular runs.

The scope limits are stated on the node: projective representations with a 7th-root twist, and `PSL_7(p^m)`
with `7 | p^m - 1`.

## 18. ex-hyperbolic-triangle-theory (615569f530)

### 18.1 `finite-simple-spectrum-gives-quotientless-hyperbolic-group`: PASS

- **Trivial finite radicals.** `H_1 = H/E(H)`, `J = C_ℓ * C_ℓ * C_ℓ` and a torsion-free Kazhdan partner `K` have
  trivial finite radical. So does `G = H_1 * J * K`.
- **Each factor `X` is a G-subgroup.**
  - A finite subgroup normalized by the infinite `X` has a fixed subtree, which `X` preserves.
  - `X` fixes exactly one vertex, so that vertex lies in the subtree.
  - The finite subgroup therefore lies in `X` and is normal there, hence trivial.
- **The quotient.** Ol'shanskii's common quotient `P` has (T) through `K` and is infinite. Suppose `S` is a finite
  simple image of `P`.
  - `S` is an image of `H`, so `ℓ ∤ |S|`.
  - `S` is also an image of `J`, injective on some `C_ℓ`, so `ℓ | |S|`. Contradiction.
- **Imports.** `olshanskii-g-subgroup-quotient-theorem` and `torsion-free-hyperbolic-kazhdan-partner-exists`, both
  citation routes with `requires: []`. Not re-read.

### 18.2 `convergent-quotient-count-decides-gromov-question`: PASS

- `X(Λ) < ∞` bounds the number of isomorphism types of simple quotients.
- A positive-weight average over a finite family is finite iff every value is finite.
- An integer-valued average below `1` has a member with value `0`.
- The title's "decides" means a reduction, as the body says.

## 19. ex-nh-deligne-hs (18160d6751): `deligne-symplectic-covers-are-not-schatten-approximated`: PASS

**Rounding lemma (R1).**
- Write `λ = ξ e^(ix)` with `|x| <= π/m`. Then `|λ - ξ| <= |x|` and `|1 - λ^m| = 2|sin(mx/2)| >= (2m/π)|x|`, so
  `|λ - f(λ)| <= |1 - λ^m|`.
- `A - f(A)` and `1 - A^m` are simultaneously diagonal, so the bound passes to Schatten norms.

**Collapse.**
- `||φ(1) - 1||_p = ||φ(1)² - φ(1)||_p -> 0`, and telescoping gives `||φ(J)^m - 1||_p -> 0`.
- `U_k = f(φ_k(J)) != 1` has an eigenvalue `ξ != 1`, so `||U_k - 1||_2 >= 2 sin(π/m)`.
- `||X||_2 <= ||X||_p` for `p <= 2`.
- Frobenius stability then gives genuine `ρ_k` with `ρ_k(J) != 1`. This contradicts Malcev together with the
  finite residual.

**Sector gap.**
- For a finitely presented Frobenius-stable group, the uniform ε–δ form follows by contradiction.
- If `ρ~(z)` is near `ζ I`, then `||ρ~(J) - I||_2 >= √d · 2 sin(π/m) - sin(π/m) > 0`, while `ρ~(J) = 1`.

**Imports, not re-read.**
- BLSW Theorems 1.1(F), 1.3, 2.10, 2.11 and Corollary 2.14. The citation route quotes pp. 2–16 verbatim.
- Deligne's finite residual.
- Malcev.

## 20. ex-hs-instability-kazhdan (e93af47046): `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`: PASS

- **§1.** `α_k(g) α_k(h) - α_k(gh) = (ρ_k(m(g,h)) - 1) α_k(gh)`.
- **(c) => (b).** `Fix_N(ρ_k)` is `Γ~`-invariant and `N` acts trivially on it, so
  `||α_k - π'_k ⊕ 1||_2 <= 2(1 - tr E_k)^(1/2)`.
- **(a) => (c).**
  - Use the bimodule representation, with the displacements on `s(F)` and on `M_0`.
  - The Kazhdan bound gives `κ||P_k - η_k|| <= δ_k`.
  - An invariant `η` satisfies `ρ_k(m) η = η`. So `1 - tr E_k = ||(1 - E_k)(P_k - η_k)||² <= δ_k²/κ²`.
- **Corollary.** Section 5 was not read line by line. Restrict a representation of `Γ_L` that is nontrivial on
  `K_L` to the orthogonal complement of `Fix(K_L)`. This gives models with `tr E = 0` that satisfy (KC1) as
  `L -> ∞`.

## 21. ex-hs-instability-extension (910e0f940f, 830e626f95, 22489455ed)

### 21.1 `compressor-extension-makes-roundable-vertex-part-invariant`: PASS at the checked steps

- **Invariance of `p_max`.**
  - `gΓg^(-1) ⊆ Γ` gives `θ_g(R) ⊆ R`.
  - A rounding of the `p`-corner restricts to the finitely many words `gγg^(-1)` with `γ in F_Γ`, so `θ_g(p)` is
    roundable.
  - `θ_g(p_max) <= p_max` with equal trace forces equality.
- **Wreath corollary.** `p_max ∈ Z(R)` commutes with the root lamp and with `σ(G)`. So its corner is a
  trace-preserving wreath model with roundable vertex, which `kt-wreath-models-never-round-on-the-vertex` excludes.
- **Not re-derived.** The join-closure of roundable projections (artifact §§1–3), and the trace lemma for groups
  that are icc modulo a finite centre.

### 21.2 `actor-extension-lifts-vertex-rounding-to-the-laurent-vertex`: PASS as an implication, at the outline level

- **K-theory.** `K_2(F_q[x_1^(±1), x_2^(±1), x_3^(±1)]) = K_2(F_q) ⊕ 3K_1(F_q) ⊕ 3K_0(F_q) = (F_q^×)³ ⊕ Z³`.
- **Step 5, checked.**
  - `Λ²Z³` acts on `ℓ²` of the character set by multiplication, and
    `||π(k)√ν_n - √ν_n||² = ∫|ω(k) - 1|² dν_n -> 0`.
  - `SL_3(Z)` acts by transport.
  - Property (T) of `Z³ ⋊ SL_3(Z)` puts `√ν_n` near an invariant vector, and invariant vectors are supported at
    `ω = 1`.
- **Not re-derived.** The seven rounding premises.

## 22. ex-q34-unit-depth (7ca62a5f5c, 03609291e6)

### 22.1 `leavitt-triangular-units-have-linear-depth-growth`: PASS

- **Finite-order degree-zero part.** `x -> x_0` is multiplicative on `⊕_(k<=0) R_k`, and
  `R_0 = ∪ M_(2^n)(F_2)` is locally finite, so `u_0` has finite order `r`.
- **Squaring.**
  - Put `v = u^r = 1 + n`. In characteristic `2`, `v^(2^k) = 1 + n^(2^k)`, with degrees `<= -2^k`.
  - A nonzero element of this form has a normal-form monomial with `|ν| >= 2^k`, and normal-form reduction never
    raises depth.
  - So `λ(v) >= 1` and `λ(u) >= 1/r`.

### 22.2 `leavitt-free-group-leading-term-forces-linear-depth`: PASS

- Bi-invariant orders make leading terms multiplicative.
- For `μ = νγ`, `(s_μ 1_E t_ν)^m = s_ν 1_(E_m) s_γ^m t_ν`, which is nonzero for all `m` iff `γ^∞ ∈ E`.
- In a free group `|g^m| >= m`, and `|g| <= 2N` on `R_N`.

### 22.3 `leavitt-heisenberg-centers-have-infinite-centralizer-rank`: PASS

- **Transcendence.** An infinite-order unit `c` is transcendental over `F_2`: if `F_2[c]` were finite-dimensional,
  `c` would be a unit of a finite ring.
- **(i)** On an `n`-dimensional `F_2(c)`-space, `det(L_a L_b) = c^n det(L_b L_a)` forces `c^n = 1`.
- **(ii)** The quantum torus over `F_2(z)` is simple, and `F_2[H_3(Z)]` is torsion-free over `F_2[z^(±1)]`.
- **(iii)** Conjugation by `t` gives `dim_K K ⊗ C_(x^k) = ρ(x)` with `K = F_2(x^(|k|))`. Then
  `C_x <= C_(x^k)` gives `|k| ρ(x) = dim_K K ⊗ C_x <= ρ(x)`, so `ρ(x) = ∞`.
