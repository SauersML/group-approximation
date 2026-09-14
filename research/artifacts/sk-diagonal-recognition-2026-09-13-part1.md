# sk-diagonal-recognition part 1: diagonal recognition fails up to G-conjugacy; the corrected target (2026-09-13)

Lane sk-diagonal-recognition (wave 11). Target: the open claim `subshift-el3-isomorphisms-recognize-diagonal-subgroups`,
here called (Rec). Everything below is UNREVIEWED and queued with sk-verify-13.

## 0. Notation

- `X` is an infinite minimal subshift with shift `T`, `A = LC(X,F_2)`, and `R = A ⋊_T Z` with `u f u^{-1} = f∘T^{-1}`.
- `G = EL_3(R)` and `L = GL_3(A) = LC(X, GL_3(F_2))`.
- `d = diag(u,1,1) ∈ GL_3(R)`.
- A **Boolean subalgebra** `B ⊆ R` is a commutative subalgebra spanned by its idempotents. Over `F_2` every element of
  such a `B` is idempotent, so `B ≅ LC(Ω,F_2)` for a Stone space `Ω`, and `M_3(B) = LC(Ω, M_3(F_2))`.
- `GL_3(B)` is the **standard diagonal** attached to `B`. (Rec) asks for `h ∈ G_Y` and a maximal commutative Boolean `B`
  with `α(L_X) = h GL_3(B) h^{-1}`.

## 1. Plan (the lane's choice)

- **(P1)** Test (Rec) against the automorphisms of `G_X` induced by `GL_3(R_X)`. Result: (Rec) is false as stated (§2).
- **(P2)** Correct the target to conjugacy by `N_Y = N_{GL_3(R_Y)}(G_Y)`. Theorem R still gives standardness (§3).
- **(P3)** Reformulate the corrected target intrinsically through a hull operator, and attack that (§4).

## 2. Theorem N

**Theorem N.**
- (a) `inn(d)` is an automorphism of `G` that is not inner.
- (b) There are no `h ∈ G` and no Boolean `B ⊆ R` with `d L d^{-1} = h GL_3(B) h^{-1}`. So (Rec) fails for the
  isomorphism `α = inn(d): G_X → G_X`.
- (c) For `k ∈ GL_3(R)`, the residue `ind(k) mod 3` is an invariant of the `G`-conjugacy class of `kLk^{-1}`. So
  `L`, `dLd^{-1}` and `d^2Ld^{-2}` are pairwise non-conjugate in `G`, and only the classes with `ind(k) ≡ 0` can
  contain a standard diagonal.

**Lemma 1 (index).** Fix `x ∈ X`, let `V = ⊕_{t∈Z} F_2^3 δ_t` with `fδ_t = f(T^tx)δ_t` and `uδ_t = δ_{t+1}`, and let
`P` be the projection onto the coordinates `t ≥ 0`.
- For `g ∈ GL_3(R)`, the compression `PgP` on `PV` is Fredholm, and `ind(g) := dim ker PgP − dim coker PgP` defines a
  homomorphism `ind: GL_3(R) → Z`.
- `ind(e_ij(r)) = 0` for all `r ∈ R` and `i ≠ j`.
- For `w ∈ R^×`, `ind(wI_3) = 3·ind_1(w)`, where `ind_1` is the same index on `⊕_t F_2δ_t`.
- `ind(d) = ind_1(u) = −1`.

*Proof.*
- Let `w_0` bound the powers `u^j` occurring in the entries of `g` and `g^{-1}`. Then `(1−P)gP` and `Pg(1−P)` are
  supported on the coordinates `|t| ≤ w_0`, so they have finite rank.
- `(PgP)(Pg^{-1}P) = P − Pg(1−P)g^{-1}P`, and symmetrically, so `Pg^{-1}P` is a parametrix and `PgP` is Fredholm.
- `PghP − (PgP)(PhP) = Pg(1−P)hP` has finite rank, and the index over a field is invariant under finite-rank
  perturbations. So `ind` is additive.
- In characteristic 2, `e_ij(r)^2 = I + 2rE_ij = I`, so `2·ind(e_ij(r)) = 0` and `ind(e_ij(r)) = 0`.
- `wI_3` acts diagonally on three copies of `⊕_t F_2δ_t`, so its index is `3·ind_1(w)`.
- `u` compresses to the unilateral shift, which is injective with a one-dimensional cokernel, so `ind_1(u) = −1`.
  `ind(d) = ind_1(u) + 2·ind_1(1) = −1`. ∎

**Lemma 2 (standard diagonals are scalar-twisted).** Let `k ∈ GL_3(R)` and let `B ⊆ R` be Boolean with
`kM_3(A)k^{-1} = M_3(B)`. Then `k = c·(wI_3)` with `c ∈ GL_3(B)` and `w ∈ R^×`, and `B = wAw^{-1}`. In particular
`ind(k) ∈ 3Z`.

*Proof.*
- `f_ij := kE_ijk^{-1}` lie in `M_3(B) = LC(Ω, M_3(F_2))` and form a complete system of matrix units.
- At each `ω ∈ Ω` they are a complete system of matrix units of `M_3(F_2)`. Pick `v ≠ 0` in the image of `f_11(ω)`;
  the matrix `c(ω)` with columns `f_11(ω)v, f_21(ω)v, f_31(ω)v` is invertible and satisfies
  `f_ij(ω) = c(ω)E_ijc(ω)^{-1}`. The choice can be made constant on the clopen sets where `f(ω)` is constant, so
  `c ∈ GL_3(B)`.
- `c^{-1}k` commutes with every `E_ij`, so `c^{-1}k = wI_3` with `w ∈ R^×`.
- Centres: `B·I = Z(M_3(B)) = k·Z(M_3(A))·k^{-1} = c(wAw^{-1}·I)c^{-1}`. Since `c ∈ M_3(B)` fixes `B·I` under
  conjugation, `wAw^{-1}·I = B·I`, that is `B = wAw^{-1}`.
- `GL_3(B) = LC(Ω, GL_3(F_2))` and `GL_3(F_2) = E_3(F_2)`. For an idempotent `e ∈ B`, the map `y ↦ ey + (1−e)I` is
  multiplicative on `M_3(F_2)`, and it sends `e_pq(1)` to `e_pq(e)`. So `c` is a product of `e_pq(e_W)` with `W ⊆ Ω`
  clopen, and `ind(c) = 0` by Lemma 1. So `ind(k) = 3·ind_1(w)`. ∎

*Proof of Theorem N.*
- **(a)** `d e_12(r) d^{-1} = e_12(ur)`, `d e_13(r) d^{-1} = e_13(ur)`, `d e_21(r) d^{-1} = e_21(ru^{-1})`,
  `d e_31(r) d^{-1} = e_31(ru^{-1})`, and `e_23(r)`, `e_32(r)` are fixed. So `dGd^{-1} = G`.
  - Suppose `inn(d)|_G = inn(g)|_G` for some `g ∈ G`.
  - Then `g^{-1}d` centralizes every `e_ij(r)`, so by the entrywise computation of Lemma 1.1 of
    `el3-root-subgroups-are-bicommutant-closed` it is a scalar in `Z(R)^× I = F_2^× I = {I}`.
  - So `d = g ∈ G` and `ind(d) = 0`, contradicting Lemma 1.
- **(b)** Suppose `dLd^{-1} = hGL_3(B)h^{-1}` with `h ∈ G`, and put `k = h^{-1}d`, so that `kLk^{-1} = GL_3(B)`.
  - `span_{F_2}L = M_3(A)` and `span_{F_2}GL_3(B) = M_3(B)`: the span of `GL_3(F_2)` is `M_3(F_2)`, and for clopen `W`
    the functions equal to a constant on `W` and to `I` off `W` span `M_3(e_WF_2) ⊕ F_2(1−e_W)I` (C3 of
    `subshift-elementary-group-rigid-supports-are-mutual-centralizers`).
  - So `kM_3(A)k^{-1} = M_3(B)`, and Lemma 2 gives `ind(k) ∈ 3Z`.
  - But `ind(k) = ind(h^{-1}) + ind(d) = 0 − 1 = −1` by Lemma 1, since `h ∈ E_3(R)`. Contradiction.
- **(c)** Suppose `kLk^{-1} = g·k′Lk′^{-1}·g^{-1}` with `g ∈ G`.
  - `n := k′^{-1}g^{-1}k` normalizes `L`, so `nM_3(A)n^{-1} = M_3(A)`.
  - Lemma 2 with `B = A` gives `ind(n) ∈ 3Z`, and `ind(n) = ind(k) − ind(k′)`.
  - The indices of `I`, `d`, `d^2` are `0, −1, −2`.
  - If `kLk^{-1} = hGL_3(B)h^{-1}` with `h ∈ G`, the argument of (b) gives `ind(k) ∈ 3Z`. ∎

**Model tests.**
- *No overreach.* `k = uI_3` has index `−3 ≡ 0`, and indeed `uLu^{-1} = L`, since `u` normalizes `A`.
- *Stability is not used.* Only additivity of the index and the two computations are used; nothing about `K_1`
  stability.
- *What survives.* The conclusion of `diagonal-recognition-makes-subshift-el3-isos-standard` holds for `inn(d)` (it
  is conjugation by an element of `GL_3(R)`), but its hypothesis with `h ∈ G_Y` fails. So the hypothesis is too strict,
  not the theorem.

## 3. The corrected target

**(Rec′).** For every isomorphism `α: G_X → G_Y` there are `k ∈ N_Y = N_{GL_3(R_Y)}(G_Y)` and a maximal commutative
Boolean `B ⊆ R_Y` with `α(L_X) = k·GL_3(B)·k^{-1}`.
- `N_Y ⊇ G_Y`, and `N_Y` contains every diagonal unit `diag(v_1,v_2,v_3)`, since conjugation by it maps `e_ij(r)` to
  `e_ij(v_irv_j^{-1})`. So `inn(d)` satisfies (Rec′) with `k = d`, `B = A`.
- **Theorem R′.** If `α(L_X) = kGL_3(B)k^{-1}` with `k ∈ N_Y`, then `inn(k^{-1})∘α: G_X → G_Y` is an isomorphism
  carrying `L_X` onto `GL_3(B)`. So the proof of `diagonal-recognition-makes-subshift-el3-isos-standard` applies
  verbatim, and `α` is standard with a conjugating element in `GL_3(R_Y)`. So `X` and `Y` are strongly orbit
  equivalent.
- **Orientation class.** By Lemma 2, `ind(k) mod 3` does not depend on the choice of `(k,B)`.
  - If `kGL_3(B)k^{-1} = k′GL_3(B′)k′^{-1}`, then `k′^{-1}k` carries `M_3(B)` onto `M_3(B′)`.
  - `B = wAw^{-1}`-type arguments show `ind(k′^{-1}k) ∈ 3Z`.
  - So every isomorphism has a well-defined orientation class in `Z/3`.

## 4. Intrinsic reformulation and attempts

**Hull.** Let `H ≤ G_Y` with `H ≅ LC(Z,Q)`, where `Q` is a finite nonabelian simple group. Write `H_V` for its
normal subgroup of elements supported in the clopen set `V`; by `locally-constant-simple-group-normal-subgroups-are-open-sets`
these are exactly its normal subgroups over clopen sets. Put:
- `H^♮_V := C_{G_Y}(H_{Z∖V})`;
- `Ĥ := ⋂_V N_{G_Y}(H^♮_V)`.

On the `X`-side, `L^♮_U = G_U` (C3) and `L̂ = L` (C4). Both notions are transported by isomorphisms, so
`H = α(L_X)` satisfies:
- **(H1)** `Ĥ = H`;
- **(H2)** `C_{G_Y}(H) = 1`;
- **(H3)** `H^♮_V` and `H^♮_{Z∖V}` are mutual centralizers (C2).

**(Rec″).** Every `H ≤ G_Y` with `H ≅ LC(Z, GL_3(F_2))` and (H1)–(H3) is `N_Y`-conjugate to a standard diagonal.
(Rec″) implies (Rec′), and it mentions only one group.

**Fake diagonals tested (sketches, not claims).**
- **Steinberg type.** When `3[1] = 8[p]` in `K_0(R_Y)` for an idempotent `p ∈ M_3(R_Y)` (for instance dyadic Toeplitz
  `Y`), a Morita copy `M_8(LC(Z,F_2)) ⊆ M_3(R_Y)` carries `LC(Z, GL_3(F_2))` through the 8-dimensional Steinberg module.
  - Its centralizer is trivial.
  - Its hull contains `LC(Z, GL_8(F_2)) ∩ G_Y`, which is strictly bigger, so (H1) fails.
- **Natural ⊕ trivial** in a Morita copy of `M_4`: the centralizer contains `diag(I_3, w)` for units `w` of the corner,
  so (H2) fails.
- **Natural with multiplicity two:** the centralizer contains `LC(Z, GL_2(F_2))`, so (H2) fails.
- **`dLd^{-1}`:** satisfies (H1)–(H3), consistent with (Rec″) and not with (Rec).

**Attempts toward (Rec″).**
- **Companions from idempotents.** Show `H^♮_V = G_Y ∩ (I + E_VM_3(R_Y)E_V)` for a Boolean family of commuting
  idempotents `E_V`. Then `Ĥ = C_{G_Y}({E_V})`, and a pointwise count of units gives the standard form.
  - Where it dies: mutual-centralizer pairs also come from non-scalar idempotents such as `E_11`, and commuting
    subgroups need not have products-zero supports.
- **Block idempotents.** Extend `α` on each finite `Q^𝒫` to `F_2[Q^𝒫] → M_3(R_Y)`, and separate the natural from the
  fake types by kernels.
  - Where it dies: `F_2[GL_3(F_2)]` is not semisimple, and its principal block contains `1`, `3` and `3*`.
- **Orbit modules** (sk-free-2: the stabilizers `H_x` are maximal, with 2-transitive coset actions on `V_x^3∖0`).
  - If every maximal subgroup of `G_Y` whose coset action is 2-transitive of linear type is an orbit-module stabilizer
    or its graph twist, then `α` induces linear bijections `V_x^3 → V_y^3`.
  - Then `α(L_X)` preserves a multiplicity-free decomposition into 3-dimensional blocks.
  - Where it dies: classifying the maximal subgroups with 2-transitive coset actions.

## 5. Graph changes in this landing

- **New established negation claim:** `subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy`, with route `-proof`
  and `requires: []`.
- **Refutation:** `refuted_by` merged onto `subshift-el3-isomorphisms-recognize-diagonal-subgroups`.
- **New open claim:** `subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer` (Rec′). It replaces the refuted
  member in `simple-kazhdan-lef-program-open-problems-conjunction`.
- **Scope merged** into `diagonal-recognition-makes-subshift-el3-isos-standard`: the conjugating element may range over
  `N_Y`, by the same proof.

**Credit.** The index of half-line compressions is the classical Fredholm index; sk-free-6 part 3 (T2) uses the same
compression for elements of `G`. No literature search on automorphisms of `E_3` over crossed products beyond a grep of
main.
