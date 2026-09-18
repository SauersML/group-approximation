# Referee report (proof review, second referee): `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` parts 1–5, and `harmonic-elimination-puts-q-in-odometer-crossed-products`

Referee: lane gq-referee-b, 2026-09-18. This is a **proof** review, not only of citations, requested by the
coordinator as the second pass after gq-referee-a (6701f023e). Reviewed: both nodes and their `-proof` routes on
main.

## Verdict

**PASS** for both.
- Parts 1–3 of the ring node (finite generation, `LC(X,Z) ⊆ R_T`, `Q ⊆ R_T`, simplicity, centre `Q`,
  `Λ_N(R_T) ⊆ {±1}`) are now double-refereed.
- So `sl3-toeplitz-harmonic-pe-groups-are-simple` rests on double-refereed inputs, apart from its own single
  referee pass (61ed26df4).
- **Part 4's `K_2` conclusion** also uses `matricial-divisibility-kills-rational-k2-symbols`, which has one referee
  pass (gq-referee-c) and which I did not review.
- **Part 5** uses only the Lee–Szczarba citation, which I verified at its secondary source earlier (e967829ec).
- **Named trust surfaces:**
  - T2: Fuglede–Kadison, from a secondary source.
  - The CBCG and Lee–Szczarba statements, which are verified at arXiv secondary sources but not at the primaries.

## A. `harmonic-elimination-puts-q-in-odometer-crossed-products`

1. `f∘γ = u_γ^{-1} f u_γ` under the convention `u_g h u_g^{-1} = h∘g^{-1}`. The `E_k` are integer polynomials in
   commuting elements of `R`. **Correct.**
2. `(f∘γ)(x) = f_K(γπ(x))` by equivariance. **Correct.**
3. `γ ↦ (γy)_M = γΓ_M · y_M` is a bijection `T_M → Γ/Γ_M`. It is right multiplication in the quotient group,
   which is well defined because `Γ_M` is normal. **Correct.**
4. For `γ ≠ γ_0`, `ℓ(γy) < M` is determined by the class `c`, so the multiset `V_M` does not depend on `x`.
   `ΠV_M = 1/D_M` and `Σ 1/v = S_M`. **Correct.**
5. `E_d = t/D_M` and `E_{d−1} = 1/D_M + tS_M/D_M`, using `Σ_v Π_{V∖v} = ΠV · Σ1/v`. So
   `E_{d−1} − S_M E_d = 1/D_M` for every value of the wild coordinate `t`, including `t = 0`. **Correct.**
6. Take `g ∈ Γ_j ∖ Γ_{j+1}`, which exists by strictness. Then `c = aΓ_M · g` agrees with `x_∞` at level `j` and not
   at `j+1`, so `m_j >= 1` and `M! | D_M`. **Correct.**
7. `1/m = (D_M/m)(1/D_M)`. **Correct.**

## B. The ring node, parts 1–5

**Part 1.**
- `u_γχ_[a]u_γ^{-1}` is the indicator of a single coordinate condition; the side depends only on the shift
  convention. Cylinders are finite products of these, and clopen subsets of `X` are finite unions of cylinders. So
  `LC(X,Z) ⊆ R_T`.
- Harmonic elimination applies:
  - the chain is `Γ = Γ(1) ⊋ Γ(2!) ⊋ Γ(3!) ⊋ ⋯`, strictly decreasing because each index `|SL_3(Z/d)|` strictly
    increases along it, and normal;
  - `π` is equivariant;
  - every `u_γ^{±1}` lies in `R_T`, generated from the `u_s^{±1}`.
- There are finitely many generators. **Correct.**

**Part 2, simplicity.**
- **Freeness.** It passes from `K` to `X` through `π`. On `K`, `gxΓ_n = xΓ_n` forces `g ∈ Γ_n`, by normality.
- **Local constancy.** For a nonempty clopen `W`, `b(W) ⊆ Q ⊆ R` is compact and countable, so it has an isolated
  point (Baire). Its preimage in `W` is a nonempty open set on which `b` is constant. **Correct**, and it needs no
  analysis of `π`-fibres.
- **Compression.**
  - After right multiplication by `u_{g_0}^{-1}`, the coefficient `b_e` is nonzero.
  - Choose a clopen `W_0 ⊆ {b_e ≠ 0}`, then a nonempty open set in `W_0` where `b_e = r ∈ Q^×`, then a point `y`
    there.
  - Freeness gives `gy ≠ y` for the finitely many `g ∈ J∖{e}`. Shrink to a clopen `W ∋ y` with `gW ∩ W = ∅`.
  - Then `χ_W x χ_W = Σ b_g χ_{W∩gW} u_g = rχ_W`, and `r` is invertible because `Q ⊆ R_T`. So `χ_W ∈ I`.
  - Minimality and compactness give translates `g_iW` covering `X`. The disjointified clopens satisfy
    `χ_{D_i} = χ_{D_i}u_{g_i}χ_Wu_{g_i}^{-1} ∈ I`, and they sum to `1`.
  - **Correct.**
- **Centre.**
  - Commuting with every `χ_V` forces `b_g = 0` off `Fix(g)`, which is empty for `g ≠ e` by freeness.
  - Commuting with every `u_γ` makes `b_e` `Γ`-invariant, hence constant by minimality, hence in `Q`.
  - Every rational constant lies in `R_T`. So `Z(R_T) = Q`. **Correct.**

**Part 3, rational scalars.**
- **The factor.** CBCG Theorem 1.3(1), verified verbatim earlier, gives `(X,ν) ≅ (K,Haar)`. So the action is
  essentially free, ergodic (transitive on every `Γ/Γ_n`) and non-atomic, and `L^∞(X,ν) ⋊ Γ` is a II₁ factor
  (group-measure-space construction).
- **The ring map.** All coefficients are bounded continuous functions, so `C(X,Q) ⋊_alg Γ → M` is a unital ring
  map.
- **The determinant.**
  - `ψ = Δ_N^N` is compatible with stabilization, by the normalized-trace scaling
    `Δ_{N+1}(diag(X,1))^{N+1} = Δ_N(X)^N`.
  - It is a homomorphism to an abelian group, so it factors through `K_1`.
  - `ψ([λ]) = |λ|`.
  - `Δ(1 + rE_ij) = exp(Re τ(rE_ij)) = 1`, since `1 + rE_ij` is `exp` of a trace-zero nilpotent.
  - So `λI_N ∈ E_N(R_T)` forces `|λ|^N = 1`, i.e. `λ = ±1`. **Correct** (T2 applies to the Fuglede–Kadison
    properties).
- **The rest.** It combines with parts 2 and 4 of `q-algebra-elementary-quotients-contain-gl-n-q`, which I passed.

**Part 4.**
- **Matrix units.** `C_d = π^{-1}(\overline{Γ(d)})` is clopen, and its translates partition `X`, because `Γ(d)` is a
  normal subgroup of finite index containing some `Γ_n`.
  - Take `e_ts = u_tχ_{C_d}u_s^{-1}` with a **fixed** set of coset representatives, containing `e`.
  - Then `e_ts e_{t's'} = δ_{st'} e_{ts'}`: the product carries the factor `χ_{C_d}χ_{s^{-1}t'C_d}`. It is nonzero
    exactly when `s^{-1}t' ∈ Γ(d)`, which for fixed representatives means `s = t'`, so `u_{s^{-1}t'} = 1`.
  - `Σ_t e_tt = 1`. So `R_T ≅ M_{n_d}(χ_{C_d}R_Tχ_{C_d})`.
  - **W1.** State that the representatives are fixed. Otherwise `u_{s^{-1}t'}` is only in `Γ(d)`.
- **Divisibility.** `n_d = |SL_3(Z/d)|`, by surjectivity of reduction. Checked:
  - `|SL_3(Z/p^k)| = p^{8(k−1)} · p^3(p^2−1)(p^3−1)`;
  - so the `p`-part is at least `p^{8k−5} >= p^k`;
  - so `d | n_d`.
  - **Correct.**
- **The `K_2` consequence** uses the matricial divisibility node, which has one referee pass and was not reviewed
  here.

**Part 5.** Every `Γ(d)^ab` is finite (Lee–Szczarba), so the Laurent-corner obstruction's hypothesis fails on
every block. **Correct** as a citation use.

## Consequence

With this pass, the chain from `R_T` to "every normal subgroup of `E_N(R_T)` is central or everything, and
`PE_N(R_T)` is infinite simple with centre of order at most 2" rests on referee-passed inputs:
- `R_T` parts 1–3, double-refereed;
- local annihilation and the Lean criterion, from my report 61ed26df4;
- the q-algebra node.

The reduction of `G` to finite presentation of `E_N(R_T)` for infinitely many `N` stands as stated.
