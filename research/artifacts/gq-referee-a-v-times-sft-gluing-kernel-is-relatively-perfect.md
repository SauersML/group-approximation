# Referee report (gq-referee-a, proof-gap lens): the V × SFT gluing kernel is relatively perfect

**Reviewed:** `v-times-sft-gluing-kernel-is-relatively-perfect` (lane bh-one-relator, e4a7fb613), read on origin/main,
with the proof inline. Notation and the copy endomorphisms come from `v-times-sft-full-groups-split-into-two-wreath-pieces`.

**Verdict: PASS.** There are four nits.
- The node is load-bearing for the P2′b routing. Items 1–3 hold as stated.
- As a result, the "central kernel plus `H_2 = 0`" attempt reduces exactly to exactness of the gluing presentation.

## (1) (R1) and (R2) from `[M_0, N_1] = 1` (the author asked about this)
- **(R1).**
  - For disjoint nonempty clopen sets `U` and `U'`, pick a proper nonempty clopen `A` with `U ⊆ A ⊆ C∖U'`. `V` is
    transitive on complementary pairs of proper nonempty clopen sets, so some `v ∈ V` has `v(C_0) = A` and
    `v(C_1) = A^c ⊇ U'`.
  - Then `vM_0v^(−1) = M_A ⊇ M_U`, computed in `M`, and `vN_1v^(−1) = N_(A^c) ⊇ N_(U')`, computed in `N_X`.
  - `v` lies in the amalgamated `V × Λ`. So conjugating the defining relation gives `[M_U, N_(U')] = 1` in `Γ~`. ✓
- **(R2).**
  - In `M`, `λ = λ|_U · λ|_(U^c)` with commuting factors, so `λ|_U = λ·(λ^(−1))|_(U^c)`.
  - `(λ^(−1))|_(U^c) ∈ M_(U^c)` commutes with `n ∈ N_U` by (R1). When `U = C` there is nothing to prove.
  - `λ` is the common element of `V × Λ`, so `λnλ^(−1)` is computed in `N_X`. ✓

## (2) The one-letter swindle in all three cases (the author asked about this)
- **The identity in `F(T)`.** `ρ_Q` is a homeomorphism. In each `X`-fibre the pieces form a complete prefix code
  `{u_i}`, and `{0u_i} ∪ {1u_i}` is again one. Locally constant dependence on `x` puts `ρ_Q` in `LC(X,V) ≤ N_X`.
  - The composite `ρ_(Q')hρ_Q^(−1)` acts as `(au w, x) ↦ (au' w, λx)`, where `Q' = h(Q)` has pieces
    `[u'] × λP`.
  - This is `copy_0(h)copy_1(h) = D(h)`. ✓
- **The case `h = fλ ∈ N_X`.**
  - `D(h) = copy_0(f)·λ|_(C_0)·copy_1(f)·λ|_(C_1)`.
  - `λ|_(C_0) ∈ M_0` commutes with `copy_1(f) ∈ N_1` by the defining relation itself. Then
    `λ|_(C_0)λ|_(C_1) = λ ∈ V × Λ`.
  - So both sides lie in `N_X ↪ F(T)`, and the identity passes to `Γ~`. ✓
- **The case `h ∈ M`, `X`-independent `Q`.** Both `ρ`'s lie in `V`, and `φ_i(M) ⊆ M`. So the identity is one inside
  `M ↪ F(T)`. ✓
- **The case `h ∈ M`, general `Q`.**
  - On a piece `[u_iv] × P`, `δ_Q = ρ_(Q^)^(−1)ρ_Q` is `u_iva w ↦ u_iav w`. So `δ_Q = ∏δ_i` with `δ_i ∈ N_([u_i])`.
  - `ρ_(Q')hρ_Q^(−1) = ρ_(Q'^) δ_(Q') h δ_Q^(−1) ρ_(Q^)^(−1)`. So it reduces to the second case once
    `hδ_Qh^(−1) = δ_(Q')` holds in `Γ~`.
  - `h = ℓg` holds in `M`. The factor `gδ_ig^(−1) = ε_i ∈ N_([u'_i])` is computed in `N_X`.
  - The other label factors `λ_k|_([u'_k])` commute with `ε_i` by (R1), since `[u'_k]` and `[u'_i]` are disjoint.
    (R2) gives `λ_i|_([u'_i]) ε_i λ_i|_([u'_i])^(−1) = λ_iε_iλ_i^(−1)`.
  - So `hδ_Qh^(−1) = ∏_i λ_iε_iλ_i^(−1)`, a product computed in `N_X`.
  - Both sides act as `(u'_iva w, λ_ix) ↦ (u'_iav w, λ_ix)` on the pieces of `Q'`, so they agree in `F(T)`. Hence
    they agree in `N_X`, hence in `Γ~`. ✓

## (3) Telescoping, and `Q_0 = Q_r` for kernel words (the author asked about this)
- Take `Q_r` refining the finitely many pullbacks of the tables of the `h_j`.
- Each `Q_j = (h_(j+1)⋯h_r)(Q_r)` is again a product partition that refines `h_j`'s table, because labels send
  cylinders to cylinders (N3).
- `Q_(j−1) = h_j(Q_j)`, so the product telescopes to `ρ_(Q_0)gρ_(Q_r)^(−1)`.
- If `π(g) = 1`, then `g` fixes every piece, so `Q_0 = Q_r` as sets of pieces.
- `ρ_Q` depends only on the set of pieces, since a piece `[u] × P` determines `u`. ✓

## (4) `σφ_0σ^(−1) = φ_1` and `v_iφ_0v_i^(−1) = φ_(0i)` (the author asked about this)
- Both sides are endomorphisms of `Γ~`, so agreement on `M ∪ N_X` suffices (N4).
- For `g ∈ M`: an identity of copies inside `M`.
- For `g = fλ`:
  - `σcopy_0(f)σ^(−1) = copy_1(f)` in `N_X`;
  - `σλ|_(C_0)σ^(−1) = λ|_(C_1)` in `M`.
- The same holds for `v_0 : 0w ↦ 00w`, and for `v_1 : 0w ↦ 01w`, each completed on the complement.
- Here `φ_(01) = φ_0 ∘ φ_1` is the copy into `C_(01)`. ✓

## (5) `x ≡ x²`, and `K = [K, Γ~]` (the author asked about this)
- `πφ_0 = copy_0π`, so `φ_0(K) ⊆ K`. Modulo `[K,Γ~]`, `K` is central.
- `k ≡ ρkρ^(−1) = φ_0(k)φ_1(k)`. Also `φ_1(k) = σφ_0(k)σ^(−1) ≡ x`. So `k ≡ x²`.
- Apply `φ_0` to item 1. The left side, `φ_0(ρ)xφ_0(ρ)^(−1)`, is `≡ x`. The right side is
  `φ_(00)(k)φ_(01)(k) = v_0xv_0^(−1)·v_1xv_1^(−1) ≡ x²`.
- So `x ≡ 1`, hence `k ≡ 1`, and `K = [K, Γ~]`. Item 3 follows. ✓

## Nits
- **N1 ((R1)).** Name the intermediate clopen `A` with `U ⊆ A ⊆ C∖U'`. Say that `vM_0v^(−1) = M_(v(C_0))` and
  `vN_1v^(−1) = N_(v(C_1))` as subgroups of `M` and of `N_X`.
- **N2 (the case `h ∈ N_X`).** Say that `Q` must also refine `h`'s table, so that `f` is constant on each `P` and `h`
  is one prefix map on each piece. Say too that `Q' = h(Q)` is a product partition, because `λ` maps cylinders of `X`
  to cylinders.
- **N3 (item 1, words).** Say in one line why each `Q_j` is a product partition refining `h_j`'s table: the image of
  a table-refining product partition is a product partition.
- **N4 (item 2).** Say that the three conjugation identities compare two endomorphisms of `Γ~`, so generators
  suffice. Record that `D` and the `φ_i` being well defined, and the commutation of `φ_0(Γ~)` with `φ_1(Γ~)`, come
  from the parent node, which is unreviewed. All three follow from (R1) and (R2) as proved here.
