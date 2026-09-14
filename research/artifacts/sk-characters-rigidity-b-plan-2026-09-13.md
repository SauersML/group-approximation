# sk-characters-rigidity-b: plan (2026-09-13)

Target: every extreme character of `G = G_X = EL_3(LC(X,F_2) ⋊ Z)` is `1` or `δ_e`. This is the open claim
`subshift-elementary-groups-are-character-rigid`. Start (b): Kakutani–Rokhlin (KR) partitions.

## Architecture (unreviewed)
1. **Putnam algebras.** For `y ∈ X`, take nested KR partitions with bases shrinking to `y` whose atoms generate
   the topology. Each tower algebra `A_n = ⊕ M_h(F_2)` is spanned by matrix units `e_{T^aB}u^{a−b}`, and
   `A_n ⊆ A_{n+1}` block-diagonally, with passage multiplicities. Put `R_y = ∪A_n`, a locally matricial
   subalgebra. Then `L_y := GL_3(R_y) = ∪ ∏ GL_{3h}(F_2)` is a locally finite subgroup of `G`.
2. **Two points generate.** If `y ≠ y'` then `R = R_y + R_{y'}`: split `u = s_n + t_n`, with shifts inside towers
   plus the short crossing `u e_{T^{-1}B_n}`. So `G = ⟨L_y, L_{y'}⟩`.
3. **(★) Crux.** The extreme characters of `L_y` are `1` and `δ_e`.
   Planned route: the Vershik–Kerov ergodic method, plus exponential character bounds for `GL_N(F_2)` in the
   support. The block-diagonal image of `g ∈ L_m∖1` at level `n` has support at least the number of passages,
   which tends to infinity. Alternative: a literature theorem on characters of unit groups of locally matrix
   algebras over finite fields.
4. **Dichotomy.** By (★), `χ|_{L_y} = a·1 + (1−a)δ_e`, with `a = χ(e_12(e_P))` for any nonempty clopen `P`,
   the same for all `y`. Let `z_K` be the projection onto `Fix(K)` in `L²(M)`, and `A = e_12(LC)`.
   - `z_{L_y} ≤ z_A` and `τ(z_{L_y}) = a = τ(z_A)`, so `z_{L_y} = z_A = z_{L_{y'}}`.
   - So `z_A` is `G`-invariant, and extremality forces `z_A ∈ {0,1}`.
   - Hence `a ∈ {0,1}`, and `a = 1` gives `χ ≡ 1`.
5. **Bessel step (`a = 0`).** Let `g ≠ 1`. There are `K` orbit-separated small clopen `V_k` with
   `x_k = e_{ij}(e_{V_k})` not commuting with `g`.
   - `[g^{-1}, x_l^{-1}x_k]` is a nontrivial element of `H_{V_k}×H_{V_l} ⊆ L_{y*}`, so `χ` vanishes on it.
   - So the vectors `π(x_kgx_k^{-1})ξ` are orthonormal with `⟨·,ξ⟩ = χ(g)`, and `K|χ(g)|² ≤ 1`.
   - Hence `χ(g) = 0`.

## Status
Steps 1, 2, 4 and 5 are elementary and still to be written out and checked. Step 3 needs an import, or its own
proof, from a source quoted verbatim. Peer: sk-characters-rigidity-a (property (T) and angles).
