
## 33. w6-v-extend (0144b771c and follow-up)

Sources:
- `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md`: Sections 1–2 at blob `d7230199`
  (0144b771c), Sections 3–5 at blob `e104a8c5` (60501cc20). Between the two blobs Sections 1–2 are unchanged, and
  only the Summary moved.
- The OPEN target `v-detecting-rank-functions-extend-to-ternary-leavitt-units` (blob `1d1d2a8b`, 4ae2882d7),
  `w6-v-extend` Attempts entry.

**Verdict: PASS on Sections 1–5 and on the Attempts entry.** No corrections. The decision-level content is the
reduction (33.1) and the location of an obstruction (33.6). Neither changes the decision: the lane found no
construction and no obstructing relation, and the target stays OPEN.

### 33.1 Reduction (artifact Section 1). PASS

- **Truth table.** The target says: some detecting function on `F_3[V]` gives a function on `F_3[G_3]` with
  `rk(1 − [z]) > 0`.
  - Its contrapositive is "link 1 ⟹ no detecting function on `F_3[V]`". By
    `simple-group-rank-functions-are-augmentation-or-detecting`, that is "link 1 ⟹ V gate".
  - The known direction is "V gate ⟹ link 1": restrict to `E ⋊ V`, apply
    `signed-thompson-z-moving-rank-functions-match-v-rank-functions` (1) ⟹ (2), then the dichotomy.
  - So the target is "link 1 ⟺ V gate". This agrees with §27.3.
- **No Hamming extension (1.2).**
  - The center of `G_3` is `⟨z⟩`. If `N ⊴ G_3` maps onto `PG_3`, then `G_3/N` is abelian, so `N = G_3` by
    perfectness. The normal subgroups are therefore `1`, `⟨z⟩` and `G_3`.
  - `ker ρ = 1` contradicts `d-ary-leavitt-groups-nonsofic-over-finite-fields` (ESTABLISHED).
  - `ker ρ = ⟨z⟩` needs `PG_3` nonsofic. Independent check: `g ↦ s_0 g t_0 + p_10 + p_11` is an injective
    homomorphism `G_3 → G_3` whose image misses `−1` (`p_10 ≠ −p_10`), so `G_3` embeds in `PG_3`.
  - `z ∉ V`, so a nontrivial Hamming model of `V` extends to no `ρ`.
- **No averaging (1.3).**
  - (T) for `L_k(1,2)^x` is closed in `leavitt-gl-equals-el-and-perfect-unit-group`, and a co-amenable subgroup of a
    Kazhdan group has finite index.
  - `GL_(2^n)(F_3) ∩ V = S_(2^n)`, since a prefix-code sum with some `|μ_i| ≠ |ν_i|` has a component of nonzero degree.
    So the index is infinite.

### 33.2 Haar values and the evaluation lift (2.1–2.2). PASS

- **Signs.** `1/2 = −1` in `F_3`, so `P^+ = −(1 + [τ])` and `P^− = [τ] − 1`, with `ev(P_α^−) = p_α`.
- **Lemma 2.1.**
  - Even patterns vanish, because `∏_(c ∈ C) τ_c = z`.
  - `V` is transitive on codes of equal size.
  - Induction gives `r_(n+1)(k) = r_n(k)/2` for odd `k <= n`, and `r_(n+1)(n+1) = β 2^(−n)`, starting from `r_1(1) = β`.
- **Proposition 2.2.**
  - `p_00 w = s_00 t_01`.
  - `[w] P_00^− [w] = P_01^−`, so `N^3 = P_00^− P_01^− [w]`.
  - Splitting over `P_1^±` leaves `q_(−,−,−)`, of rank `>= β/4`.

### 33.3 Fock lift and splitting (2.3–2.4). PASS

- **Proposition 2.3.**
  - `ev(e_(+−)) = p_01`.
  - `e_(+−)[w] = [w] e_(−+)` gives `N_F^2 = 0`.
  - `τ_00 w = w τ_01` gives `[τ_00] N_F [τ_00] = −N_F`.
  - Cylinder-preserving `v` commute with `w`.
- **Splitting.** `t_010 s_001 = 0`, so `x = x_0 x_1`.
- **Proposition 2.4.**
  - `P_00^+ g = 0`, `f_1 g = 0` and `f_0 g = g`, so `D g = −[w_0] g`.
  - `g >= q_(+,−,−,+,−)` gives rank `>= β/16`.

### 33.4 Unipotent classes (artifact Section 3). PASS

- **Lemma 3.1.**
  - (a) `t_0 s_0 = 1`, so `ker(s_0 t_1) = ker t_1 = p_0 R`, using `t_1 p_0 = 0`. The image is `s_0 R = p_0 R`.
  - (b) `t_01 = t_1 t_0` and `t_01 s_00 = t_1 s_0 = 0`, so `n^2 = 0`. Also `ker n = (1 − p_01) R`, `im n = p_00 R`, and
    `t_1 : p_1 R → R` has inverse `s_1`.
  - (c) `−2 = 1`, so `(c_3 − 1)^2 = 1 + c_3 + c_3^2`, the all-ones matrix. It is nonzero because `M_3(F_3) → R` is
    injective.
  - **Invariants.** `n_(ugu^(−1)) = u n_g u^(−1)`, so kernel and image are carried by left multiplication by `u`. The
    quotient is `0` for `T(0,1)` and `≅ R` for `x`, and `n^2 ≠ 0` for `c_3`.
- **Proposition 3.2.**
  - `(u − 1)^2` has the single entry `ac`, which gives 12 regular elements and 14 square-zero ones. The square-zero
    ones have rank one: `a = 0` leaves one column and `c = 0` one row.
  - **Conjugator.** `v = s_0 t_00 + s_10 t_01 + s_11 t_1` and `v^(−1) = v^*` give `v s_00 = s_0` and `t_01 v^* = t_10`, so
    `v x v^(−1) = T(0,10)`.
  - `c_3` has minimal polynomial `X^3 − 1 = (X − 1)^3`. Rank functions are conjugation invariant.
- **3.3.**
  - A group of order 54 gives a free `F_3[X]/(X − 1)^3`-module, with profile `(2/3, 1/3)`.
  - The natural module gives `(1/3, 0)` on the rank-one elements.
  - The Frobenius inequality `2 rk(N^2) <= rk(N) + rk(N^3)` holds.
  - `z`, `T(0,10)` and `T(10,11)` have `|σ| <= |κ|`, as in the depth-monotone node, line 29.

### 33.5 Fock parity and the intertwiner (Section 4). PASS

- `Λ(τ_c) e_S = (−1)^|S ∩ c| e_S`, so `Λ(P_c^−)` is `−2 = 1` on odd `S` and `0` on even `S`.
- **Proposition 4.1.**
  - (a) `Λ_2(x)` sends `e_01` to `e_01 + e_00`, and the extra term dies if `00 ∈ S`. `Λ_2(X_F)` corrects exactly when
    `00 ∉ S` and `01 ∈ S`, replacing `e_01` in place. So the two agree.
  - (b) `x = x_0 x_1` at level three, and `Λ_3` is multiplicative. For `S = {001, 010}`: `Λ_3(X_F) e_S = e_S`, but
    `Λ_3(x) e_S = e_S + e_001 ∧ e_000`. The cell parities are `(+, −, −, +)`.
- **4.3.** The cited nodes are ESTABLISHED on main at `1da285e70`:
  - `level-unit-hnn-extensions-have-anti-central-rank-models`, with `B_g = {a ∈ L : g a g^(−1) ∈ L}` at line 17;
  - `fock-local-letters-extend-level-models-with-disjoint-commutation`;
  - `natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter`;
  - `exterior-tensor-powers-are-asymptotically-free`.

### 33.6 Obstruction location and the weakly finite version (Section 5). PASS

- **5.1.** `σ_reg(x) = σ_reg(x_0) σ_reg(x_1)` is a level identity, and `X_(v_i)` intertwines on `B_(v_i) ∋ x`. So the
  HNN model satisfies splitting.
- **Corollary 5.1.** Under the hypothesis, the target's conclusion is "not link 1".
- **The gloss "kills every extension", checked.**
  - `{g : rk(1 − [g]) = 0}` is a normal subgroup. If it contained `V` it would be `G_3`, and then `β = 0`.
  - So a function with `β > 0` restricts to a non-augmentation function on `V`, which is detecting by the dichotomy.
  - Killing every extension of every detecting `rk_V` is therefore link 1.
- **5.3.** With `B_g` as in 33.5, `B_(v,v') ⊆ B_(v v')`, and both commutant bullets recompute.
- **Proposition 5.2.**
  - The kernel misses `V \ 1`, so it is `1` or `⟨z⟩`.
  - `e = (1 − u)/2 ≠ 0` is central in the image.
  - `(A + (1 − e)1_n)(B + (1 − e)1_n) = 1_n` gives `BA = e 1_n`.
  - `linear-sofic-group-algebra-is-stably-finite` exists. `ternary-anti-central-summand-has-no-weakly-finite-image` is
    OPEN, as the Status bullet treats it.
- **Candidates.** Untested and not verified here. `T(00,1)` has `|σ| > |κ|`.

### 33.7 The Attempts entry (target node). PASS

- It matches the artifact on each item: the reduction, both bounds, the classes, the intertwiner, the two letters
  outside `L`, and the weakly finite version.
- "Via `ker n / im n`" separates `T(0,1)` from `x`, and `n^2 ≠ 0` separates `c_3`. Both are `R_R` invariants, so no
  change is needed.
- **Scope.** Every bound is a multiple of `β`, and no item forces `β = 0` or rank triviality. Plan 1 and the gate stay
  OPEN.
