# sk-normalizer-recognition: plan (2026-09-14)

Lane sk-normalizer-recognition (after the 09-14 reboot). Target: the open claim
`subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer` (Rec′). This is a plan artifact, with no claims.

## 0. Setting and what a yes gives

- `X`, `Y` are infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, `G_X = EL_3(R_X)`, `L_X = GL_3(LC(X,F_2)) = LC(X,Q)`
  with `Q = GL_3(F_2)`.
- For clopen `U`, `G_U = G_X ∩ (I + M_3(e_U R_X e_U))` and `L_U` is the part of `L_X` supported in `U`.
- `α: G_X → G_Y` is an isomorphism and `N_Y = N_{GL_3(R_Y)}(G_Y)`.
- (Rec′) asks: `α(L_X) = k·GL_3(B)·k^{-1}` with `k ∈ N_Y` and `B` a maximal commutative Boolean subalgebra of `R_Y`.
  - By Theorem R′ this gives `M_3(R_X) ≅ M_3(R_Y)`, so `X` and `Y` are strongly orbit equivalent.

**Reviewed inputs to consume** (C-numbers from `subshift-elementary-group-rigid-supports-are-mutual-centralizers`,
PASS sk-verify-3):
- C2: `C_G(G_U) = G_{X∖U}`.
- C3: `C_G(L_{X∖U}) = G_U`.
- C4: `N_G(G_U)` is the set of elements commuting with `E_U = e_U I_3`, and `⋂_U N_G(G_U) = L`.
- The index `ind: GL_3(R) → Z`, which vanishes on `E_3(R)` (sk-diagonal-recognition Lemma 1, PASS sk-verify-16).
- Internal cancellation of idempotents in `M_n(R_Y)` (sk-algebraic-putnam item 5, PASS sk-verify-16).
- `K^0(Y,T)` is torsion-free (a dimension group).

## 1. Route A: rigid supports come from idempotents (main route)

Every group-theoretic statement in C2–C4 transports along `α`. Write `A_U := α(G_U) ≤ G_Y`. Then:
- `A_U` and `A_{X∖U}` are mutual centralizers;
- `α(L_X) = ⋂_U N_{G_Y}(A_U)`.

**(A1) Idempotent realization.** There is a Boolean family of commuting idempotents `E′_U ∈ M_3(R_Y)` with
`E′_{X∖U} = I − E′_U`, `E′_{U∩W} = E′_U E′_W`, and `A_U = G_Y ∩ (I + E′_U M_3(R_Y) E′_U)`.

**(A2) Reduction (to prove): (A1) ⇒ (Rec′).**
- By the Y-side version of C4 for arbitrary full idempotents, `α(L_X) = C_{G_Y}(𝔅)`, where `𝔅 = span{E′_U} ≅ LC(X,F_2)`.
- The commutant algebra `𝒞 = C_{M_3(R_Y)}(𝔅)` has unit group, intersected with `G_Y`, isomorphic to `LC(X,Q)`, which is
  locally finite. Use this to force `𝒞` to be pointwise `M_3(F_2)`: twisted commutants contain full-group intertwiners
  of infinite order.
- A complete system of matrix units `f_ij ∈ 𝒞` gives `3[f_11] = [I] = 3[E_11]` in `K_0(R_Y)`. Torsion-freeness gives
  `[f_11] = [E_11]`, and internal cancellation gives `k ∈ GL_3(R_Y)` with `k E_ij k^{-1} = f_ij`. So
  `𝒞 = k M_3(B) k^{-1}`.
- Last, `k ∈ N_Y`, or a replacement: Theorem R′ only needs `inn(k^{-1})∘α` to land in a group where its centralizer
  computations run.

**(A1) tools.**
- **Frobenius support idempotents.** `F21 = C_7 ⋊ C_3 ≤ Q` has odd order, so for constant copies `F21_W ≤ L_W` the sum
  `P_W := Σ_{k ∈ α(F21_W)} k` is an idempotent in `M_3(R_Y)`: the projection onto `Fix(α(F21_W))` along
  `[M, α(F21_W)]`, where `M = R_Y^3`.
  - On the X-side `Σ_{k∈F21_W} k = e_{X∖W} I_3`, since `F21` has no fixed vector on `F_2^3`.
  - So `P_{X∖U}` is the candidate for `E′_U`.
- **Commutation.** `A_U` commutes with `α(F21_{X∖U})`, so `A_U` commutes with `P_{X∖U}`: sums of commuting elements
  commute. So `A_U` preserves `P_{X∖U}M` and `(I − P_{X∖U})M`.
- **Simplicity dichotomy.** `G_U ≅ EL_3` of the corner ring, which is again a minimal subshift crossed product
  (induced system), so `A_U` is simple. So `A_U` acts on each invariant piece trivially or faithfully.
- **Type distinction.** Corner groups of non-full idempotents, such as `E_11` or `E_11 + E_22`, pair a GL_1-type group,
  amenable because `R_Y^× ≅ [[T]]`, with a GL_2-type one. Both `A_U` and `A_{X∖U}` are Kazhdan and non-amenable (EJZ). So
  only full idempotents with full complement can occur.
- **Gap to close.** `A_U` acts trivially on `(I − P_{X∖U})M`, and `A_U` is all of `G_Y ∩ (I + P M P)`.
  - The first needs `(α(g) − I)(α(k) − I) = 0` for `g ∈ G_U`, `k ∈ α(F21_{X∖U})`. That is a ring relation. The plan
    is to derive it from simplicity plus C3: `A_U = C(α(L_{X∖U}))`.

## 2. Route B: block theory of `F_2[GL_3(2)]` (for A2 and a module form of A1)

- `F_2[Q]` has the principal block (simple modules `1, 3, 3*`) and a defect-zero Steinberg block (`8`).
- `F21`-restrictions: `3` and `3*` have no fixed vector; `1` and `8` do. So `[M, α(F21_V)]` has only `3` and `3*`
  composition factors under `α(Q_V)`, once `Q_V` preserves it.
- Needed: `Ext^1_{F_2Q}(3,3) = 0 = Ext^1(3*,3*)`, to check at source or compute (MeatAxe/GAP on MSI). Then pure-type
  pieces are semisimple, `[M, α(Q_V)] ≅ 3 ⊗ P_V` with `P_V` right `R_Y`-projective, and the mixed `3/3*` case is
  excluded as in Theorem R Step 5(iii) (simplicity of `R_Y`).

## 3. Route C (fallback): `K^0` and GPS directly, bypassing standardness

- `e_13(1_A) ~ e_13(1_B)` in `G_X` iff `[1_A] = [1_B]` in `K^0(X,T)` (`subshift-el-transvection-conjugacy-full-group-equivalence`,
  PASS sk-verify-14).
- If the set of clopen transvections is recognized intrinsically, together with disjointness (commutation with opposite
  root elements), then `(K^0, K^0_+, [1])` transports and GPS 1995 gives strong orbit equivalence.
- Where it is hard: classical characterizations of transvections fail here. Products of two conjugate transvections can
  have infinite order, for example `e_12(1)e_21(u)`.

## 4. Order of work

1. Prove the commutation and dichotomy lemmas of §1 rigorously, and the type distinction (amenable GL_1-type corners).
2. Attack the gap of §1: trivial action of `A_U` on `[M, α(F21_{X∖U})]`.
3. (A2) with the `K_0` and cancellation argument.
4. Record every failure as Attempts on the open node, and queue proven lemmas in `$SK2/queue/verify.txt`.
