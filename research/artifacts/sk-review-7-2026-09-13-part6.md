# SK review 7, part 6: non-confined test subgroups for C*-simplicity of G_X (sk-cstar-simple)

Lane `sk-verify-7`, 2026-09-13 ~21:55 CDT. Queue entries 60–63. I re-derived every step by hand; the matrix identities were multiplied out entry by entry.
Scope:
- These are the four test-subgroup claims only.
- The target `subshift-elementary-groups-are-cstar-simple` and the import `cstar-simple-iff-amenable-subgroups-not-confined` keep their own status. A C*-simplicity conclusion needs every amenable confined subgroup ruled out, not only these test subgroups.

## 0. Verdicts

| Claim | Verdict |
|---|---|
| `elementary-root-subgroups-over-crossed-products-are-not-confined` + route | PASS |
| `locally-constant-gl-n-subgroup-is-not-confined` + route | PASS |
| `topological-full-group-images-in-el3-are-not-confined` + route | PASS |
| `cut-stabilizer-subgroups-of-el3-are-not-confined` + route | PASS |

No FAIL, no GAP.

## 1. Root subgroups
**Lemma A.** If the conjugates of `H` intersect pairwise trivially, a finite `P ⊆ G∖{1}` meets at most `|P|` of them. So `H` is not confined. Checked.

**Lemma B.** `u^N − u^M = u^M(u^d − 1)`. If `r ≠ 0` has top exponent `max S`, then `u^dr` has a nonzero coefficient at `max S + d`, which `r` lacks (`d > 0`); for `d < 0` use `min S`. Checked.

**Reduction.** Subgroups of a non-confined subgroup are non-confined, and confinement is conjugation invariant. Weyl elements move `e_12(R)` to any `e_ij(R)`. Checked.

**Conjugation.**
- `k_Ne_12(r)k_N^{-1} = [e_31(u^N),e_12(r)]e_12(r) = e_32(u^Nr)e_12(r) = I + u^NrE_32 + rE_12`, since `E_32E_12 = 0`.
- If two such conjugates agree for `N ≠ M`, the `(1,2)` entries give `r = r′`, and the `(3,2)` entries give `(u^N−u^M)r = 0`. So `r = 0`.
- Checked.

## 2. Locally constant matrices over F_2
**Step 1.**
- `ψ_i(x) = (1−e_{C_i})I + e_{C_i}x` is multiplicative on constant matrices, because they commute with `e_{C_i}`.
- `GL_n(F_2) = E_n(F_2)`.
- The factors have disjoint supports, so they commute.
- Checked.

**Step 2.** `c_N = ∏_i d_i(u^{s_iN})` with `s_i − s_{i−1} = ε_i` and `s_n = 0`, and each `d_i` is a Whitehead element. Checked.

**Step 3.**
- `(c_Ngc_N^{-1})_{ij} = (g_ij∘T^{−ε_iN})u^{(ε_i−ε_j)N}`.
- For `i ≠ j` the exponents differ, so equality of two conjugates forces the off-diagonal entries to be `0`.
- The diagonal entries are units of `LC(X,F_2)`, hence `1`.
- So the intersection is trivial. Checked.

**W10 (wording, route model test).**
- The scope note is correct: over `F_q`, `q > 2`, Step 3 fails.
- The route's model test says the torus `diag(LC(X,F_3^×))` *commutes* with every `c_N`. In fact `c_N diag(f_i) c_N^{-1} = diag(f_i∘T^{−ε_iN})`, so the torus is only *normalized* by `c_N`. Its constant part `diag(F_3^×)` does commute.
- Either way the torus lies in every conjugate, so the conclusion stands. Suggested wording: "is normalized by every `c_N`".

## 3. Images of the topological full group
- `(I+sE_31)p = p + saE_31`, since row 1 of `p` is `(a,0,0)`.
- `psE_31 = sE_31`, since column 3 of `p` is `(0,0,1)^T`.
- So `k_Npk_N^{-1} = p + u^N(a−1)E_31`.
- Equal conjugates share their diagonal. Then Lemma B gives `a = 1`, and injectivity of the first coordinate gives `p = I`.
- Checked.

**Instances.**
- `diag(w_g,1,1)` and `diag(w_g,u^{−I(g)},1)` have first coordinate `w_g`, which determines `g`: the `u^n` coefficient of `w_g` is `e_{n_g=n}`.
- These maps are homomorphisms into `G`: that is the content of `topological-full-group-embeds-in-subshift-elementary-group`.
- That node is reviewed: `research/artifacts/sk-review-2-2026-09-13-part4.md` row 18 gives PASS for the node and its proof (landed 43d31d65e).
  - §18 re-derives `w_gw_h = w_{gh}`, Corollary A (`[[T]]' → G_X` is an injective homomorphism) and the index map.
  - Its line 47 re-derives that `diag(w_g,u^{−I(g)},1)` is multiplicative slot by slot and injective, with index 0.
- The node's header still reads "unreviewed; queued with sk-referee-2", and it carries no review line. That is stale bookkeeping for the steward, not a gap.
- So the Instances hold as stated.

## 4. The cut stabilizer
**Representation.** `π_y(u)δ_t = δ_{t+1}` and `π_y(f)δ_t = f(T^ty)δ_t`, so `π_y(ufu^{-1})δ_t = f(T^{t−1}y)δ_t = π_y(f∘T^{-1})δ_t`. Checked.

**Lemma C.**
- `(c^{-1}qc)_{ij} = u^{−N_i}q_iju^{N_j}`, with `π_y = σ^{−N_i}π_y(q_ij)σ^{N_j}`.
- Preserving the two cut subspaces means sending `V^{≥N_j}` into `V^{≥N_i}` and `V^{<N_j}` into `V^{<N_i}`.
- **Case `N_i − N_j ≥ w+L+1`.**
  - The times `t+k_0`, `t ∈ [N_j, N_i−w−1]`, run through an interval of length `≥ L+1`. So one of them is a visit of `{r_{k_0} = 1}`.
  - `δ_t ∈ V^{≥N_j}`, while the image has a nonzero component at `t+k_0 < N_i`.
- **Case `N_j − N_i ≥ w+L+1`.** Symmetric, with `t ∈ [N_i+w, N_j−1]`.
- Checked.

**Lemma D** (B. H. Neumann covering). The induction on the number of distinct subgroups is correct. Checked.

**Lemma E.**
- `l = I + e_VE_12 + e_{V′}E_13 = l^{-1}`.
- `lql^{-1} = q + (e_Vb + ae_V)E_12 + (e_{V′}c + ae_{V′})E_13`, because `NqN = 0`.
- Membership in `lDl^{-1}` fixes the pattern of `p` and requires `φ_p(V) = p_12` and `φ′_p(V′) = p_13`.
- Clopen sets under `Δ` form a group with `e_{VΔV_2} = e_V + e_{V_2}`, so the bad pairs for `p` form a coset of `ker φ_p × ker φ′_p` or are empty.
- If no good pair existed, the group of pairs would be a finite union of such cosets. Lemma D then gives finite-index kernels for some `p`, and Lemma F gives `a = b = c = 1`, so `p = I`.
- Checked.

**Lemma F.**
- **Case `a ∉ LC(X,F_2)`.**
  - `ae_W = Σ_ma_me_{T^mW}u^m`, so the `u^j` coefficient of `(1+e_W)ae_W` is `a_je_{T^jW∖W}`.
  - If `φ(W) = 0`, then `(1+e_W)ae_W = (1+e_W)e_Wb = 0`.
  - Choose `2(k+1)` distinct points `z_i, T^{-j}z_i` (no periodic points). Neighbourhoods `W_i ∋ T^{-j}z_i` avoid all `z_{i′}` and have `T^jW_i ⊆ O`.
  - Every nonempty union `W` contains some `T^{-j}z_i`, so `z_i ∈ T^jW∖W`, and `φ(W) ≠ 0`.
  - So the index is at least `2^{k+1}` for every `k`.
- **Case `a ∈ LC`.** A unit of `R` in `LC(X,F_2)` is `1`, and then `φ(W) = e_W(b+1)` is nonzero for unions of disjoint `W_i` inside the support of a coefficient of `b+1`.
- Checked.

**Theorem.**
- `Q = l^{-1}Pl` consists of non-diagonal elements, each with a nonzero off-diagonal entry.
- `c = diag(u^{−K},1,u^K)` is a Whitehead element in the `(1,3)` block, with pairwise cut differences `K, K, 2K ≥ K > w+L+1`.
- Lemma C gives `c^{-1}qc ∉ S_y`, so `P ∩ (lc)S_y(lc)^{-1} = ∅`.
- Checked.

**Tower groups.**
- `π_y(e_{T^aW′}u^{a−b})δ_t` is nonzero only if `T^{t−b}y ∈ W′ ⊆ B`, i.e. `t−b` is a visit time `τ_m` with `0 ≤ b < h`. Then `t` and `t+a−b` both lie in `[τ_m,τ_{m+1})`.
- `τ_0 = 0` is an endpoint, so the tower algebra preserves the cut.
- Checked.

**W11 (tower groups).** `L_y = ⋃_n GL_3(A(𝒫_n)) ∩ G` is a group, and locally finite, when the partitions `𝒫_n` refine each other with bases shrinking to `y`, which is the standard choice. Without refinement, read `L_y` as the subgroup generated by the `GL_3(A(𝒫_n)) ∩ G`. It still lies in `S_y`, so the conclusion is unchanged.

**Other routine facts used, all checked.**
- `S_y` is a group: `V^{<0} ⊕ V^{≥0}` is the whole space, so an invertible `g` that maps each summand into itself maps it onto itself.
- Gap bound: forward orbits of a minimal system are dense, so finitely many `T^{-s}O` with `s ≥ 0` cover `X`.
- `D` includes non-locally-constant units such as `u^K`, and Lemma F handles general units.

## 5. Scope and what this does not give
- These are four non-confined families. They are consistent with, but do not prove, C*-simplicity of `G_X`, which needs every amenable confined subgroup ruled out, or another criterion.
- Not re-read at source: Kennedy / Le Boudec–Matte Bon's characterization, and the amenability (Juschenko–Monod) and simplicity (Matui) of `[[T]]'`, cited in the Consequence of claim 3.
- No novelty check.

## 6. Concurrence
- `sk-verify-13` landed an independent review of the same four claims (`research/artifacts/sk-verify-13-2026-09-13-part1.md`, landed bb61db6741): PASS on all four. I concur.
- Their one condition is that the Instances of claim 3 rest on `topological-full-group-embeds-in-subshift-elementary-group`, which they call unreviewed. See §3 for why that condition is already met.
