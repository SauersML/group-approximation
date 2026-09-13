# EX review, backlog, part 4: the Q3.4 lanes and ex-nh-fresh (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`.

## 7. ex-q34-leavitt-hs (5c1973dd19, c2c211d999, 002c44b8c8, d5e68d9885, b43722425f, 7cf93ea999, 63fcfd037a)

### 7.1 `thompson-elements-are-undistorted-in-leavitt-unit-group`: PASS

- **Subadditivity.** `t_β s_γ` is `s_γ'`, `t_β'` or `0`. So `(s_α t_β)(s_γ t_δ)` is `s_(αγ') t_δ` or
  `s_α t_(δβ')`, of depth `<= N + M`.
- **Depth bounds germs.**
  - In the sequence module, `x in R_N` sends `e_ξ` into the span of the `e_(α σ^|β| ξ)`.
  - Let `ξ` be aperiodic. Two representations `α σ^b ξ = α' σ^(b') ξ` with `|α| - b != |α'| - b'` would
    make `ξ` eventually periodic. So the prefix-change degree of a germ is at most `N`.
  - Every cylinder contains aperiodic points, so the bound holds everywhere.
- **Linear growth.** The imported slope is `e(z) = L_r (⌊z/u⌋ + 1) + S_(r,z)`, with `S` bounded and
  base `2n - 1 = 3`. It gives `ℓ(g^z) >= |e(z)|`, hence `|g^z|_S >= (L⌊z/u⌋ - C)/L_S`.
- **Corollary.** A central commutator satisfies `c^(m²) = [a^m, b^m]`, and in `BS(1,k)`,
  `x^(k^j) = t^j x t^(-j)`.
- **Imports, not re-read.** Bleak et al., arXiv:1107.0672v3, Theorem 1.3 and the §8 slope computation;
  finite generation of `Q`.

### 7.2 `thompson-v-has-no-heisenberg-subgroup` and the three imports: PASS

The imports are `thompson-v-cyclic-subgroups-are-undistorted`, `thompson-v-powers-have-linearly-growing-slope`
and `leavitt-algebras-l-k-1-n-are-simple`.
- From `ab = cba` with `c` central, `a b^m = c^m b^m a`, so `[a^m, b^m] = c^(m²)`.
- `BS(1,k) ≅ Z[1/k] ⋊ Z`.
- For the rose `R_n`, `n >= 2`, the only hereditary saturated sets are trivial, and every loop has another
  loop as an exit.

### 7.3 `leavitt-unit-groups-over-finite-fields-mutually-embed`: PASS

- **(a)** `0, 10, ..., 1^(n-2)0, 1^(n-1)` is a complete binary prefix code with `n` words.
- **(b)** `ρ(F_q)` commutes with `s_i I_k` and `t_i I_k` in `M_k(L_(F_p)(1,2))`. So
  `L_(F_q)(1,2) = F_q ⊗_(F_p) L_(F_p)(1,2)` maps in, and prefix codes give `M_k(L) ≅ L`.
- **(c)**
  - The `2n' - 2` words `00, ..., 0(n'-1), 1, ..., n'-2` are pairwise incomparable, and
    `Σ S[w]T[w] = e`.
  - `Y_a X_b = δ_ab e`, `X_0 Y_0 + X_1 Y_1 = e`, and all `X_a, Y_a` lie in `eAe`.
  - `u ↦ ψ(u) + 1 - e` is multiplicative, because `ψ(u)(1 - e) = 0`.
- Simplicity makes every unital map out of `L_K(1,m)` injective.

### 7.4 `leavitt-north-south-thompson-unit-has-cyclic-centralizer`: PASS

All five items re-derived from the artifact.
- **Module.** `(S[α]T[β]f)(x) = 1_[α](x) f(β σ^|α| x)` satisfies `T[i]S[j] = δ_ij` and
  `S[0]T[0] + S[1]T[1] = 1`. It is faithful by simplicity.
- **Lemma 1.** The prefix replacement `β -> α` scales measure by `2^(|β| - |α|) <= 2^N`.
- **Lemma 2.** For clopen `A`, `1_A = Σ_w S[w]T[w]`, and `x e_A = 0` by faithfulness. So `x` kills every
  aperiodic Chen module, and its annihilator is a proper ideal.
- **Step 1.**
  - `c^(-am) h` equals `1` on `c^(-am)[0^K]`, whose measure tends to `1`.
  - But `g c^(-am) f` has support measure `<= T 2^N Σ_i μ(c^(i-am) D) -> 0`, since
    `μ(c^(-k) D) = 2^(-(k+2))`.
- **Step 2.**
  - Only terms `(α, 0^b)` contribute on `[0^(ak) 1]`.
  - A term with a `1` in `α` lands in some `c^i D` with `|i| <= N`: `α = 0^n 1...` gives `c^n D`, and
    `α = 1^n 0...` or `α = 1^n` gives `c^(-(n-1)) D`. These terms cancel for large `k`, because
    `g c^(ak) f = c^(ak) g f` is supported far out.
  - A term `(0^(a'), 0^b)` contributes exactly `c^(ak + a' - b) f`.
- **Item 3.**
  - For `a, b > 0`, Case A contradicts the support-measure bound.
  - Case B gives `2^(-(am-1)) μ(D) <= T' 2^(N') C 2^(-bm)`, so `b <= a`. Symmetry gives `a = b`.
  - For `b < 0`, the roles of `p` and `q` swap, with `μ(c^(-|b|m)[1^K]) = 2^(-|b|m) μ([1^K])`.
- **Items 4 and 5.**
  - `N_Q(<c>) -> Aut(Z)` has kernel `<c>`.
  - The relative commutant of `L(<c>)` is spanned by elements with finite `<c>`-orbits, and these lie in
    `C_Q(c^n) = <c>`.

### 7.5 Graph status

- `leavitt-unit-group-has-no-integer-heisenberg-subgroup` and
  `kun-thom-wreath-does-not-embed-in-leavitt-unit-group` are OPEN.
- The mutual `refuted_by` edges with `kun-thom-wreath-embeds-in-leavitt-unit-group` join two open claims,
  so neither fires.
- The depth-growth experiment is labelled as evidence only.

## 8. ex-q34-kt-double (2dc316605c, 155a3a90b7, fbd2aefb11, 6447c33169, 4a45710df2, 29be6c5fe0, 218c71f3f9, 347722257b, b7dcc5c7f0)

### 8.1 `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`: PASS as an implication

- **Step 2.**
  - `a_K = θ(e_K)` commutes with `θ(K) ⊇ σ(Γ)`.
  - If `Γ <= gKg^(-1)` for all `g`, then `N <= core_G(K) <= K`, which is excluded. So some `γgK != gK`.
  - The two lamps are then distinct involutions with `τ(e_(gK) e_(γgK)) = 0`, so
    `||a_(γgK) - a_(gK)||_2 = √2`.
  - Hence `σ(g) a_K σ(g)^* = a_(gK)` does not lie in `R`.
- **Step 3.** It uses the four rounding premises as landed.
  - Their routes exist, and §2, §5 and §24 of `review-backlog-2026-09-12.md` pass parts of the chain.
  - The remaining premises were not re-derived here.
- **Step 4.** Flexible stability of `Γ` gives (H1) at `σ|Γ`.

### 8.2 `fournier-facio-vertex-rounding-fails-at-every-model`: PASS

- A finitely generated infinite simple group has only trivial finite-dimensional unitary representations
  (Malcev).
- Rounding transports `π_n(s) = 1` to `σ(s) = 1`, because the padding has weight `(n' - n)/n' -> 0`.

### 8.3 `kt-sofic-monomial-commutant-core-is-normalized`: PASS

- **Monomial rigidity.** `m σ(γ) m^* = π d'` with `π = p σ(γ) p^(-1)`, and
  `||π_n d'_n - σ_n(γ)||_2² >= 2 d_H(π_n, σ_n(γ))`.
- **Doubling.**
  - `s_e` is a permutation that commutes with `σ2(Γ)` exactly when `e in R`.
  - `σ2(t) s_e σ2(t)^(-1) = s_(σ(t) e σ(t)^(-1))` holds exactly.
  - Kun--Thom 4.1 then gives invariance of `D ∩ R`.
- **Items 3--4.** `E_(N_σ)(z)` lies in `N_σ <= R` and is carried into `R`. Also `σ(Γ) <= B_σ`, so
  `A_σ <= R`.

### 8.4 Open claims

- `kt-sofic-models-normalize-vn-commutants` is OPEN.
- Its route requires `kt-centralizer-normalization-hs`, which is OPEN at tip `b3083ac22`, so the route does
  not fire. Each of that claim's four routes needs an open premise:
  - `hyperlinear-groups-kill-rigid-compression-defects`, which is open, and whose own route runs back
    through the claim;
  - `approximate-collapse-for-kt-compressor`, which has no route;
  - `hs-stable-vertex-rounding-for-every-model`, which is open and has no route.

## 9. ex-q34-collapse (f8d1346e0f, d48bdd179a, 0ae866b209)

### 9.1 `block-monomial-hs-models-sofic-mod-amenable-soft-kernel`: PASS

- **Hamming comparison.** Columns with `σ(i) != σ'(i)` send `e_i ⊗ v` to orthogonal unit vectors. So
  `||M - M'||_2² >= 2 d_H`, with equality against `(u; id)`.
- **Soft kernel.**
  - On the soft kernel, the block-diagonal parts represent `ρ` inside `∏_ω (ℓ^∞_n ⊗ M_k)`, which
    satisfies `S_(2k)`.
  - A regular trace makes the generated algebra `L(A)`.
  - A `II_1` summand would contain a unital `M_m` with `m > k`, where `S_(2k)` does not vanish. So `L(A)`
    is type I, hence injective, and `A` is amenable.

### 9.2 `leavitt-units-admit-no-bounded-block-monomial-hs-model` and `kt-double-admits-no-bounded-block-monomial-hs-model`: PASS

- A simple nonsofic group, or a nonsofic group with trivial amenable radical, has trivial soft kernel.
- The permutation-part map of `R^x` into a universal sofic group is trivial.

### 9.3 `coarse-frame-normalizers-are-near-block-monomial`: PASS

- `A_ji = Tr(p_j u p_i u^*)/k` is doubly stochastic, and `def(f)² = ||f||_2² - (1/n)||Af||²`.
- Random signs give `(1/n) Σ_i Σ_j A_ji² >= 1 - δ²`, and `Σ_j A_ji² <= max_j A_ji`.
- The argmax is injective where the maximum exceeds `1/2`, since row sums are `1`. The remaining indices
  have density `<= 2δ²`. Hence `(1/n) Σ_i (1 - A_(σ(i) i)) <= 3δ²`.
- **Polar parts.** `Tr((1 - |b_i|)²) <= Tr(1 - |b_i|²) = k(1 - A_(σ(i) i))`. The total error is `2√3 δ`.

### 9.4 `standard-identity-witnesses-force-block-displacement` and `leavitt-unit-microstates-are-asymptotically-primitive`: PASS

- **Displacement bound.**
  - Amitsur--Levitzki applies to the block-diagonal parts.
  - Distinct products are trace-separated, so `||Σ_π sgn(π) U_(w_π)||_2² >= (2k)! - 4((2k)!)² δ`.
  - Together these force `ρ² >= 1/(4k²(2k)!) - O(δ)`, that is displacement `>= 1/(8k²(2k)!) - C_k δ`.
- **Amplification.** Tensor powers add Hamming defects and multiply fixed-point densities.

### 9.5 `monomial-rank-models-are-sofic-over-every-field`: PASS at the outline level

- The column-Hamming comparison `|Q|/2 <= rank(A - B) <= |Q|`, from the components of a degree-two
  multigraph.
- A generic character of the finitely generated label group.
- Torsion points are dense in closed subgroups of tori.
- Elek--Szabó amplification.
- The artifact's sections 1--2 were not read line by line.

### 9.6 Imports and open claims

- **`hyperlinear-groups-closed-under-free-products`.** Brown--Dykema--Jung Corollary 4.5 and Pestov
  Theorem 8.5, as quoted. Not re-read.
- **`hyperlinear-implies-sofic-via-frame-extraction`.**
  - It targets `hyperlinear-implies-sofic` and requires the OPEN
    `hyperlinear-groups-admit-masa-normalizing-microstates`, so it does not fire.
  - Its logic is correct: `H * Z` with `H != 1` has no nontrivial abelian normal subgroup.
- **`monomially-hyperlinear-groups-are-sofic`.** OPEN, with Attempts.

## 10. ex-nh-fresh (adb21d1503, b7443a2125)

### 10.1 `period-doubling-subshift-algebra-is-its-own-matrix-ring`: PASS

- **Matrix units.** `T^(a-b) P_c = P_(c+a-b)`, so
  `E_ab E_cd = χ_(P_a) χ_(T^(a-b) P_c) u^(a-b+c-d) = δ_bc E_ad`.
- **Decimation.**
  - On the even phase, the odd coordinates are `ν_2(i) mod 2 = 0`.
  - For even `a`, `ν_2(a + 2i) = 1 + ν_2(a/2 + i)`, so `1 + x(2i) ≡ ν_2(a/2 + i) mod 2`.
  - So decimation lands in `X` and intertwines `T²` with `T`. It is injective, and onto by minimality.
- **Rank.** `EL_3(M_2(R)) = EL_6(R)`, by block commutators.

### 10.2 The route-map artifact

It is an artifact only and changes no status. I did not re-audit it here.
