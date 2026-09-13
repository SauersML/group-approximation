
## 32. w6-v-extend: lifts of the transvection (artifact Sections 1–2)

Source: `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md` (0144b771c, blob `d7230199`).
No claim node landed with it. Sections 3–5 land separately. The target
`v-detecting-rank-functions-extend-to-ternary-leavitt-units` stays OPEN, and no verdict here is decision-level.

### 32.1 Reduction (artifact Section 1). PASS

- **Truth table.** The target node says: some detecting function on `F_3[V]` gives a function on `F_3[G_3]` with
  `rk(1 − [z]) > 0`. Its contrapositive is "link 1 ⟹ no detecting function on `F_3[V]`". By
  `simple-group-rank-functions-are-augmentation-or-detecting`, that is "link 1 ⟹ V gate". The known direction
  (restrict to `E ⋊ V`, then `signed-thompson-z-moving-rank-functions-match-v-rank-functions` (1) ⟹ (2), then
  the dichotomy) is "V gate ⟹ link 1". So the target is "link 1 ⟺ V gate". This agrees with §27.3.
- **No Hamming extension (1.2).**
  - The center of `G_3` is `⟨z⟩`. If `N ⊴ G_3` maps onto `PG_3`, then `G_3/N` is abelian and `N = G_3` by
    perfectness. So the normal subgroups are `1`, `⟨z⟩`, `G_3`.
  - `ker ρ = 1` contradicts `d-ary-leavitt-groups-nonsofic-over-finite-fields` (ESTABLISHED).
  - `ker ρ = ⟨z⟩` needs `PG_3` nonsofic. Independent check: `g ↦ s_0 g t_0 + p_10 + p_11` is an injective
    homomorphism `G_3 → G_3` whose image misses `−1` (`p_10 ≠ −p_10`), so `G_3` embeds in `PG_3`. This is the
    route of `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`.
  - `z ∉ V`, so a nontrivial Hamming model of `V` extends to no `ρ`.
- **No averaging (1.3).** Property (T) for `L_k(1,2)^x` is a closed theorem in
  `leavitt-gl-equals-el-and-perfect-unit-group`, and a co-amenable subgroup of a Kazhdan group has finite index.
  `GL_(2^n)(F_3) ∩ V = S_(2^n)`, because a prefix-code sum `Σ s_(μ_i) t_(ν_i)` with some `|μ_i| ≠ |ν_i|` has a
  nonzero component of nonzero total degree. So the index is infinite. This is a remark, not a claim.

### 32.2 Haar values and the evaluation lift (2.1–2.2). PASS

- **Signs.** `1/2 = −1` in `F_3`, so `P^+ = −(1 + [τ])` and `P^− = [τ] − 1`, with `ev(P_α^−) = p_α` and
  `ev(P_α^+) = 1 − p_α`.
- **Lemma 2.1.**
  - Even patterns vanish because `∏_(c ∈ C) τ_c = 1 + Σ p_c = −1 = z`.
  - `V` is transitive on codes of equal size, and the refinement identities are `(1 ± ab)/2` expanded.
  - Induction: for odd `k <= n`, `r_(n+1)(k) = r_n(k)/2`. For `k = n + 1` odd (`n >= 2`),
    `r_(n+1)(n+1) = r_n(n−1) − r_(n+1)(n−1) = β 2^(−n)`. The base is `r_1(1) = r(e_−) = β`.
- **Proposition 2.2.**
  - `w = s_00 t_01 + s_01 t_00 + s_1 t_1` gives `p_00 w = s_00 t_01`.
  - `[w] P_00^− [w] = P_01^−`, so `N^3 = P_00^− P_01^− [w]` and `(1 + N)^3 = 1 + N^3`.
  - Splitting `P_00^− P_01^−` over `P_1^±` leaves `q_(−,−,−)`: three minus signs on three cells, rank `>= β/4`.

### 32.3 Fock lift and splitting (2.3–2.4). PASS

- **Proposition 2.3.**
  - (a) `ev(e_(+−)) = (1 − p_00) p_01 = p_01`, and `w p_01 = s_00 t_01`.
  - (b) `e_(+−) [w] = [w] e_(−+)`, so `N_F^2 = [w]^2 e_(−+) e_(+−) = 0`. Hence `X_F` has order three.
  - (c) `τ_00 w = w τ_01`, `[τ_01] e_(+−) = −e_(+−)` and `e_(+−) [τ_00] = e_(+−)` give `[τ_00] N_F [τ_00] = −N_F`.
    In `R`, `t_01 p_00 = 0` gives `(1 + p_00) s_00 t_01 (1 + p_00) = 2 s_00 t_01`.
  - (d) If `v(00a) = 00u(a)` and `v(01a) = 01u(a)`, then `v w v^(−1) = w` and `v` fixes both cylinders. In `R`,
    `v s_00 = s_00 ū`, and `t_01 v^(−1) = ū^(−1) t_01` by `v^(−1) = v^*`.
- **Splitting.**
  - `t_010 s_001 = t_0 t_1 s_0 s_1 = 0` kills the cross terms, so `x = x_0 x_1`. Also
    `X_i = [v_i] X_F [v_i]^(−1) = 1 + [w_i] f_i`, and `w_0 w_1 = w` with disjoint supports.
- **Proposition 2.4.**
  - `[τ_00] = [τ_000][τ_001]` acts on `g` by `−1`, so `P_00^+ g = 0` and `e_(+−) g = 0`.
  - `f_1 g ∋ P_001^+ P_001^− = 0`, and `f_0 g = g`. So `D g = −[w_0] g` and `rk(D) >= rk(g)`.
  - `g >= q_(+,−,−,+,−)`: three minus signs on five cells, rank `>= β/16`.
- **Scope.** Only these two lifts are shown to fail (artifact 2.5, "Not claimed"). Every bound is a multiple of
  `β`, so nothing here proves triviality for a ring with rank models.
