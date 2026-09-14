# Character rigidity of G_X, part 2: the dichotomy, the Bessel step, the theorem

Lane sk-characters-rigidity-b, 2026-09-13. UNREVIEWED. Notation as in part 1: `G = EL_3(LC(X,F_2) ⋊ Z)`, `L_y`,
`L_n`, `A(𝒫_n)`, GNS `(π, H = L²(M,τ), ξ)`.

## 4. The trivial part is central

For a subgroup `K = ⋃_n K_n` with finite `K_1 ⊆ K_2 ⊆ …`, put `p_{K_n} = |K_n|^{-1} Σ_{x∈K_n} π(x) ∈ M`.
- `p_{K_n}` is the projection onto the `K_n`-fixed vectors of `H`.
- The `p_{K_n}` decrease strongly to `p_K`, the projection onto the `K`-fixed vectors. So `p_K ∈ M` and
  `τ(p_K) = lim τ(p_{K_n})`.
- `x p_K = p_K` for `x ∈ π(K)`.

**Lemma 5.** Let `χ` be a character of `G` with constant `c` from Lemma 4, and let `A := e_12(LC(X,F_2))`. Then
`π(x) p_A = p_A = p_A π(x)` for all `x ∈ G`, so `p_A` is a central projection of `M`, and `τ(p_A) = c`.

*Proof.*
- **Traces.** `A = ⋃ A_n` with `A_n = e_12(span{e_D : D a level of 𝒫_n}) ⊆ L_n` finite and `|A_n| → ∞`. By
  Lemma 4, `τ(p_{A_n}) = (1 + (|A_n| − 1)c)/|A_n| → c`. Likewise `τ(p_{L_n}) → c`. So `τ(p_A) = c = τ(p_{L_y})`.
- **Equality.** `A ⊆ L_y` gives `p_{L_y} ≤ p_A`. Since `τ` is faithful, `p_{L_y} = p_A`. The same holds at a second
  point `y' ≠ y`, so `p_{L_{y'}} = p_A`.
- **Invariance.** `π(x)p_A = p_A` for `x ∈ L_y ∪ L_{y'}`, hence for all `x ∈ G` by Lemma 2.
- **Centrality.** Taking adjoints, `p_A π(x) = p_A`, so `p_A` commutes with `π(G)''`. ∎

## 5. The Bessel step

**Lemma 6.** Let `χ` be a character of `G` such that `χ(h) = 0` for every `y ∈ X` and every `h ∈ L_y ∖ {1}`. Then
`χ = δ_e`.

*Proof.* Fix `g ≠ 1`, and let `w ≥ 0` bound the exponents in the entries of `g` and `g^{-1}`. As in the note,
call a clopen `V` *small* if `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`, and every `f∘T^i` is constant on `V`, where
`|i| ≤ w` and `f` is a coefficient of an entry of `g` or `g^{-1}`.

(a) **Local constants.**
- For small `V`, `g e_V = Σ_{p,q,a} γ^{pq}_a e_{T^aV} u^a E_pq` with constants `γ ∈ F_2`, and likewise for `e_V g`.
- Call `V` *trivial* if `g e_V = e_V I_3 = e_V g`. By uniqueness of coefficients this is the condition
  `γ = δ_{pq}δ_{a0}` on the constants.
- So triviality is inherited both ways: a nonempty clopen `V' ⊆ V` is trivial iff `V` is.
- Partitioning `X` into small sets shows that some small `V` is nontrivial, since otherwise `g = gI_3 = I_3`.

(b) **Noncommuting roots.** If `V` is small and nontrivial, some `x = e_ij(e_V)` does not commute with `g`.
- Otherwise `g e_V E_ij = e_V E_ij g` for all `i ≠ j`, so `g_{pi}e_V = 0` for `p ≠ i`, and `e_V g_{jq} = 0` for
  `q ≠ j`, and `g_{ii}e_V = e_V g_{jj}`.
- Comparing the coefficient of `u^a` in the last identity: for `a ≠ 0` the supports `T^aV` and `V` are disjoint, so
  both sides vanish. For `a = 0` both sides equal a constant times `e_V`.
- So `g e_V = diag(ε_i) e_V` with `ε_i ∈ F_2`. Invertibility of `g` forces `ε_i = 1`, otherwise
  `g·(e_V E_ii) = 0`.
- Hence `g e_V = e_V I_3`, and symmetrically `e_V g = e_V I_3`: `V` is trivial.

(c) **Conjugation lands in one tower group.**
- For small `V`, put `ε_{ab} = e_{T^aV}u^{a−b}` (`|a|,|b| ≤ w`) and `d = 3(2w+1)`.
- Let `ψ_V: M_d(F_2) → M_3(R)` be `E_{(p,a),(q,b)} ↦ ε_{ab}E_pq`, and `H_V := {I_3 − ψ_V(I_d) + ψ_V(B) : B ∈ GL_d(F_2)}`.
- For `x = e_ij(e_V)`, the entries of `g^{-1} x g − I_3 = g^{-1} e_V E_ij g` are sums of `f u^a e_V f' u^b =
  f e_{T^aV}(f'∘T^{-a})u^{a+b} ∈ {0, ε_{a,−b}}`. So `g^{-1}xg ∈ H_V`, and also `x ∈ H_V`.

(d) **Disjoint towers.** Let `V, V'` be small with `T^aV ∩ T^bV' = ∅` for `|a|,|b| ≤ w`.
- Then `ψ_V(M_d)·ψ_{V'}(M_d) = 0`, so `H_V` and `H_{V'}` commute elementwise and `H_V ∩ H_{V'} = 1`.
- Let `y* ∉ ⋃_{|a|≤w} T^a(V ∪ V')`, and take a nested system at `y*` with `B_n ∩ T^aV = ∅` for `|a| ≤ w`.
  - The segment from `T^bV` to `T^aV` never enters `B_n`. So once the levels `T^aV` are unions of levels of
    `𝒫_n`, `ε_{ab} = Σ E^C_{c+(a−b),c}` lies in `A(𝒫_n)`.
  - The same holds for `V'`. Hence `H_V H_{V'} ⊆ L_{y*}`.

(e) **Many far-apart sets.**
- A nontrivial small `V` is uncountable. Choose `K` points in it with pairwise disjoint orbit segments
  `{T^a x : |a| ≤ w}`, small neighborhoods `V_1, …, V_K ⊆ V` with pairwise disjoint towers, and a point `y*`
  outside all towers (shrinking the `V_k` if needed).
- Each `V_k` is nontrivial by (a), so by (b) some `x_k = e_{i_kj_k}(e_{V_k})` does not commute with `g`.

(f) **Orthogonality.**
- Put `g_k = x_k g x_k^{-1}` and `v_k = π(g_k)ξ`. For `k ≠ l`, with `y = x_l^{-1}x_k`,
  `⟨v_k, v_l⟩ = χ(g_l^{-1}g_k) = χ(x_l^{-1}(g_l^{-1}g_k)x_l) = χ(g^{-1} y g y^{-1})`.
- `g^{-1}yg y^{-1} = (g^{-1}x_l g·x_l)(g^{-1}x_k g·x_k)`. The factors lie in the commuting groups `H_{V_l}` and
  `H_{V_k}`, and the second factor is not 1 because `x_k` does not commute with `g`.
- By (d), this element lies in `L_{y*} ∖ {1}`, so `χ` vanishes on it. The `v_k` are orthonormal.

(g) **Bessel.**
- `⟨ξ, v_k⟩ = \overline{χ(g_k)} = \overline{χ(g)}`, so Bessel's inequality gives `K|χ(g)|² ≤ ‖ξ‖² = 1`.
- `K` is arbitrary, so `χ(g) = 0`. ∎

## 6. Proof of Theorem R

Let `χ` be a character, with `c` from Lemma 4 and `p_A` from Lemma 5.
- **c = 1.** `p_A = 1`, so `π(x) = 1` for all `x`, and `χ ≡ 1`.
- **c < 1.** `χ_2(x) := τ((1 − p_A)π(x))/(1 − c)` is a positive definite class function with `χ_2(e) = 1`: it is
  `⟨π(x)(1−p_A)ξ,(1−p_A)ξ⟩/(1−c)`, since `p_A` is central.
  - Since `p_Aπ(x) = p_A`, `χ(x) = c + (1 − c)χ_2(x)`.
  - By Lemma 4, `χ_2(h) = (χ(h) − c)/(1 − c) = 0` for every `h ∈ L_y ∖ {1}` and every `y`.
  - So `χ_2 = δ_e` by Lemma 6, and `χ = c·1 + (1 − c)δ_e`. ∎

## 7. Corollaries

- **(R1)** The extreme characters of `G_X` are `1` and `δ_e`. So every II_1 factor representation of `G_X` with
  finite trace generates `L(G_X)`, and there is no other II_1 factor representation of this kind.
- **(R2) Invariant random subgroups.** `G_X` is infinite and simple, so it has no proper finite-index subgroup.
  The general principle of `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §1
  (hypotheses: no proper finite-index subgroup, and every character is `b·1 + (1−b)δ_e`) gives
  `IRS(G_X) = {(1−b)δ_{1} + b δ_{G_X}}`. So every probability-preserving action of `G_X` is essentially free off its
  global fixed set.
- **(R3)** sk-characters' Theorem A (18375ec10e) follows. A character with `χ(e_12(e_P)) → 1` as `‖P‖ → 0` has
  constant `c = 1`.
- **(R4)** The full C*-algebra `C*(G_X)` has exactly two extreme tracial states: the trivial one and the canonical
  trace.
- **(R5)** The proof never uses finite generation or property (T). It holds for `EL_n(LC(X,F_2) ⋊ Z)`, `n ≥ 3`, for
  every infinite minimal Cantor system.

## 8. Model tests and firewalls

- **Periodic `X`.** `T` has periodic points, so tower heights stay bounded and Lemma 1(ii) fails. The conclusion
  fails too: `EL_3` over `M_p(F_2[t^{±1}])` has finite congruence quotients, whose characters pull back.
- **Aperiodic, not minimal.** Uniform recurrence in Lemma 1(iii) fails. The conclusion fails: `G_X → G_Y` for a
  closed invariant `Y ⊊ X`, and `δ_e` of `G_Y` pulls back to a character that is neither 1 nor `δ_e`.
- **Topological full groups.** `[[T]]'` has the Dudko–Medynets characters `∏μ_i(Fix γ)`. The analogue of Lemma 3
  fails for alternating groups in diagonal limits: the normalized fixed-point character does not decay with
  absolute support, only with the fraction moved. The decisive input here is exponential decay of `GL_N(F_2)`
  character ratios in the absolute support (Larsen–Tiep).
- **Natural limits.** `GL_∞(F_q) = ⋃ GL_n(F_q)` has the Thoma–Skudlarek characters `q^{−m·rank(g−1)}`. There the
  support of a fixed `g` stays bounded along the limit. In `L_y` it grows linearly in the tower height (Lemma 1′),
  which kills them.
- **Over `F_q`, `q > 2`** (not claimed). `GL_{3h}(F_q)` is not quasisimple, and determinant or centre characters do
  not decay. So a statement over `F_q` needs the centre and `K_1` handled separately.

## 9. Credit and novelty (bounded check)

- **Imports.** Larsen–Tiep Theorem A (arXiv:2403.09046) is the only import. The class-size and degree bounds of
  Lemma 3 are elementary.
- **Context.**
  - Kakutani–Rokhlin towers and Putnam's subalgebra `A_y` of `C(X) ⋊ Z`, here in algebraic form.
  - Dudko–Medynets (characters of full groups and of inductive limits of symmetric groups, arXiv:1105.6325,
    2602.16885).
  - Thoma and Skudlarek (`GL_∞(q)`).
  - Carderi–Thom (Lemma 1.4, used in sk-characters' Theorem A).
- **Search.** Five web searches (diagonal limits of finite linear groups, Leinen–Puglisi, Zalesskii, Larsen–Tiep,
  Peterson–Thom) found no character classification for `EL_n` over crossed products or for simple Kazhdan LEF
  groups. Zalesskii's survey *Group rings of simple locally finite groups* (NATO ASI 471) was not read.
