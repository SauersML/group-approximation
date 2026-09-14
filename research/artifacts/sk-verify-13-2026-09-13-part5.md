# SK verify 13, part 5: the cut stabilizer is amenable and normalish, and the BKKO routes (sk-cstar-simple-2)

Lane sk-verify-13 (wave 10), 2026-09-13. Queue lines 10–11 (landed 6d669709f6). Main marked both Cairn-only. Queue lines 12
and later belong to sk-verify-14.

Targets: `cut-stabilizers-of-el-n-are-locally-finite-normalish` (+ route `cut-stabilizers-el-n-locally-finite-normalish-proof`)
and `subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology` (+ route `subshift-el-groups-vanishing-l2-bounded-cohomology-proof`).

Every step was re-derived by hand. BKKO quotes were re-checked against the arXiv:1410.2518 e-print, fetched to
`/scratch.global/sauer354/sk/sk-verify-13/bkko/src/main.tex`.

## 0. Verdicts

| claim | verdict |
|---|---|
| `cut-stabilizers-of-el-n-are-locally-finite-normalish` | PASS |
| `subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology` | PASS (items 1–2 imports verified verbatim; item 3 re-derived) |

**Scope.** These results are negative for the method, not for the question: they show that BKKO's sufficient criteria
cannot decide C*-simplicity of `G_X`. That is consistent with part 1 (`S_y` is not confined), since normalish and not
confined are compatible. `subshift-elementary-groups-are-cstar-simple` correctly stays OPEN. The Haagerup
per-element-averaging remark in the merged Attempt 7 was not checked here.

## 1. The cut stabilizer

**Membership.** `π_y(g)` acts entrywise on `F_q^{(Z)} ⊗ F_q^n`. So `g` preserves `V^{<0}` and `V^{≥0}` iff each entry does,
i.e. lies in `R_y`. `S_y` is a subgroup: an invertible operator preserving both summands of a direct sum has an inverse that
preserves them too.

**Crossing conditions.**
- `π(f_ku^k)δ_t = f_k(T^{t+k}y)δ_{t+k}`, and distinct `k` give distinct basis vectors, so `r ∈ R_y` iff each term `f_ku^k`
  lies in `R_y`.
- For `k > 0`, crossing upward means `t ∈ [−k,−1]`, so `f_k` must vanish at `T^jy` for `j = t+k ∈ [0,k−1]`.
- For `k < 0`, crossing downward means `t ∈ [0,−k−1]`, so `j ∈ [k,−1]`.

**Local finiteness.** Choose the clopen `B ∋ y` so that the finitely many `f_k` vanish on the required `T^jB` (locally
constant, zero at `T^jy`).
- Minimality gives bounded return times. Refine the bases so that every `f_k` is constant on every level.
- `f_ku^k = Σ c·e_{T^aW}u^k` with `e_{T^aW}u^k = u^ke_{T^{a−k}W}`. This is the matrix unit `E_{a,a−k}(W)` when
  `0 ≤ a−k < h(W)`.
- **No crossing.**
  - `k > 0`, `a < k`: `T^aW ⊆ T^aB` with `a ∈ [0,k−1]`, where `c = 0`.
  - `k < 0`, `a−k ≥ h(W)`: `T^aW = T^{−j}(T^{h(W)}W) ⊆ T^{−j}B` with `j = h(W) − a ∈ [1,|k|]`, where `c = 0`.
- **Tower algebras.** `A ≅ ⊕_W M_{h(W)}(F_q)` lies in `R_y`. The same computation as part 1 §4 applies: `t` and
  `t + a − b` lie in one return interval, and `0` is an endpoint. So `R_y` is a directed union of finite rings.
- Finitely many elements of `S_y` and their inverses have entries in one `A`, so they lie in the finite group `GL_n(A)`.

**Window lemma.**
- `π(fu^k)` shifts positions by `k`, so `π(t)V^{≥0} ⊆ V^{≥−W_0}`.
- `V^{≥W_0} = π(t)π(t^{-1})V^{≥W_0} ⊆ π(t)V^{≥0}`.
- For `v ∈ π(t)V^{≥0}`, write `v = v_J + v_+` with `v_+ ∈ V^{≥W_0} ⊆ π(t)V^{≥0}`. Then `v_J ∈ π(t)V^{≥0} ∩ V^{[−W_0,W_0)}`.
- The same holds for `V^{<0}`.

**Normalish.**
- `Z` is a clopen neighbourhood of the `2W_0` orbit points with `X∖Z ≠ ∅`. `X∖Z` is infinite, because `X` is perfect.
- `K_Z ⊆ G` pointwise: `l = Σ_i e_{C_i}g_i` with `g_i ∈ SL_n(F_q) = E_n(F_q)`, and each factor `(1−e_{C_i})I + e_{C_i}g_i`
  is a product of `e_jk(λe_{C_i})`.
- `K_Z` is infinite: disjoint clopen pieces of `X∖Z` carry distinct nontrivial elements.
- `π(l)` acts position by position. It is the identity at positions in `[−W_0,W_0)`, because `T^sy ∈ Z` there, and it
  preserves `V^{≥W_0}` and `V^{<−W_0}`.
- So it preserves `π(t_i)V^{≥0}` and `π(t_i)V^{<0}`, which gives `t_i^{-1}lt_i ∈ S_y`.
- Modulo the finite centre, images of infinite sets stay infinite, and amenability passes to quotients.

**Wording (0 lines).** Step 1 of the route should state `A ⊆ R_y` explicitly. Claim item 1 ("directed union of tower
algebras") uses it.

**Model tests.** A finite orbit breaks the choice of `Z`. Linear groups with trivial amenable radical have no amenable
normalish subgroup (BKKO, Theorem `thm:linear-groups-non-amenability-normalish`, l.699–700). `G_X` is not linear, since it
is f.g., infinite and simple, and Mal'cev applies. So there is no conflict.

## 2. Vanishing and failure of (CS)

**Items 1–2 (imports), verbatim at source.**
- `\begin{prop}\label{betti}` (l.626–627): "If $G$ contains an amenable normalish subgroup, then $\beta_n^{(2)} = 0$ for
  every $n \geq 0$".
- Mixing modules (l.643): "the stabilizer subgroup … is finite for every $x \in E \setminus \{0\}$. Examples … $\ell^p(G)$
  for $1\le p < \infty$".
- `thm:trivial-bdd-cohomology` (l.647–649): "$H_b^n(G,E)$ is trivial for every $n \geq 0$".
- The citation nodes' quotes match.
- With `S_y` amenable and normalish (§1, also modulo the centre over `F_q`), both items follow. For `n = 0`,
  `E^G = 0`, since `G` is infinite and `E` is mixing.

**Item 3, re-derived against the definition.**
- l.939–941: "For every weakly regular unitary representation $\pi$ … there exists an SOT-neighborhood $U$ of the identity
  … such that $\pi^{-1}(U) \subset R_a(G)$".
- `G` is simple, infinite and Kazhdan, hence non-amenable, so `R_a(G) = 1`.
- `π = λ_{G/S_y}` is weakly regular because `S_y` is amenable (BKKO l.945).
- A neighbourhood `U` contains `{T : ‖(T−I)ξ_j‖ < ε, j ≤ k}`. Choose `η_j` finitely supported on cosets `s_1S_y, …, s_pS_y`
  with `‖ξ_j − η_j‖ < ε/3`.
- `g ∈ ⋂_i s_iS_ys_i^{-1}` fixes each `s_iS_y`, so `π(g)η_j = η_j` and `‖(π(g)−I)ξ_j‖ ≤ 2ε/3 < ε`.
- That intersection is infinite, so `π^{-1}(U)` is infinite and not inside `R_a(G) = 1`. So (CS) fails.
- This is BKKO's own one-line remark (l.945: "if $H$ is normalish, then $\pi(G)$ is clearly not discrete"), written out.

**Consequence, correctly stated on the node.**
- BKKO Theorem `thm:betti` needs non-vanishing, and the Proposition at l.942 needs (CS), so neither applies.
- `BS(m,n)` (Remark l.948) shows that an amenable normalish subgroup is no obstruction to C*-simplicity.

## 3. Queue state
Lines 1–11 are served: parts 1–5. Lines 12 and later are sk-verify-14's (main's split, ~22:15).
