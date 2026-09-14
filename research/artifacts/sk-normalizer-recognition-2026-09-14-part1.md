# sk-normalizer-recognition part 1: Frobenius support idempotents and a Boolean realization (2026-09-14)

Lane sk-normalizer-recognition. Target: (Rec′), `subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer`.
Everything below is UNREVIEWED.

## 0. Setting

- `X`, `Y` are infinite minimal subshifts, `R_X = LC(X,F_2) ⋊_T Z`, and `G_X = EL_3(R_X)`. The same holds for `Y`.
- `M = R_Y^3` (columns), with `GL_3(R_Y)` acting on the left and `R_Y` on the right. So `GL_3(R_Y)` acts faithfully by
  right `R_Y`-linear maps.
- `α: G_X → G_Y` is an isomorphism.
- `Q = GL_3(F_2) = E_3(F_2)`. `F21 = ⟨c, s⟩ ≤ Q` is a Frobenius subgroup of order 21: `c` is a Singer cycle of order 7
  and `s` has order 3 with `scs^{-1} = c^2`. `c` acts on `F_2^3 ≅ F_8` by multiplication by a primitive element, so
  `F21` has no nonzero fixed vector on `F_2^3`.
- For clopen `V ⊆ X` and `q ∈ Q`, `q_V ∈ L_X` equals `q` on `V` and `I` off `V`. So `F21_V := {q_V : q ∈ F21} ≅ F21`
  for `V ≠ ∅`, and `F21_V ≤ E_3(e_V R_X e_V)`, since `q` is a product of `e_ij(1)` and `e_ij(e_V)` is the corresponding
  root element of the corner.
- `E3_V := E_3(e_V R_X e_V)` sits in `G_X` as `I + M_3(e_VR_Xe_V)`-supported matrices.

## 1. Frobenius support idempotents

**Definition.** `S_V := I + Σ_{k∈α(F21_V)} k ∈ M_3(R_Y)` (over `F_2`).

**Lemma S (basic).** Let `K = α(F21_V)` and `P_V = Σ_{k∈K} k`.
- (a) `P_V` is idempotent, `kP_V = P_Vk = P_V` for `k ∈ K`, `P_V M = Fix(K)` and `(I − P_V)M = [M,K] := Σ_k Im(k − I)`.
  So `S_V = I − P_V` is the idempotent onto `[M,K]` along `Fix(K)`.
- (b) On the X-side (`α = id`), `S_V = e_V I_3`.
- (c) `S_∅ = 0`, and `S_V ≠ 0` for `V ≠ ∅`.
- (d) If `V ∩ W = ∅`, then `S_V` and `S_W` commute.
- (e) Every element of `G_Y` commuting with `α(F21_V)` commutes with `S_V`.

*Proof.*
- (a) `P_V² = |K|·P_V = P_V`, since `|K| = 21` is odd. `kP_V = P_V` because left multiplication permutes `K`, and
  similarly on the right. `P_V` fixes `Fix(K)` pointwise and maps into `Fix(K)`. `Σ_k(k − I) = P_V − 21·I = P_V − I`, so
  `(I − P_V)M ⊆ [M,K]`. And `P_V(k − I) = 0`, so `[M,K] ⊆ ker P_V = (I − P_V)M`.
- (b) `Σ_{q∈F21} q_V = e_{X∖V}·21·I + e_V·Σ_{q∈F21} q`. The inner sum is the projection onto `Fix_{F21}(F_2^3) = 0`, so
  it vanishes and `S_V = e_V I`.
- (c) `F21_∅ = {1}`. For `V ≠ ∅`, some `k ∈ K` is not `I`, and `M` is a faithful module, so `[M,K] ≠ 0`.
- (d) `F21_V` and `F21_W` have disjoint supports, so they commute, and so do their images and the sums.
- (e) Such an element commutes with each summand. ∎

## 2. The unconditional dichotomy

Fix clopen `U` with `∅ ≠ U ≠ X`. Put `A_0 := α(E3_U)`, `K := α(F21_{X∖U})` and `K′ := α(F21_U) ≤ A_0`.

**Lemma D.** `A_0` acts trivially on `S_{X∖U}M` if and only if `S_U S_{X∖U} = 0`.

*Proof.*
- `E3_U` commutes with `G_{X∖U} ⊇ F21_{X∖U}` (C2 of `subshift-elementary-group-rigid-supports-are-mutual-centralizers`,
  PASS). So `A_0` commutes with `K`, and by Lemma S(e) it commutes with `S_{X∖U}`. So `A_0` preserves
  `S_{X∖U}M = [M,K]` and `(I − S_{X∖U})M = Fix(K)`.
- `K` and `K′` commute, so `S_U` and `S_{X∖U}` commute. `M` splits into the four joint pieces
  `M_{ab} = S_U^a(I−S_U)^{1−a} S_{X∖U}^b (I−S_{X∖U})^{1−b} M`.
  - `K′` acts trivially on `M_{0b}` and without nonzero fixed vectors on `M_{1b}`, since `Fix(K′) ∩ [M,K′] = 0` by
    Lemma S(a).
- (⇒) If `A_0 ⊇ K′` is trivial on `S_{X∖U}M ⊇ M_{11}`, then `M_{11} ⊆ Fix(K′) ∩ [M,K′] = 0`.
- (⇐) If `M_{11} = 0`, then `S_{X∖U}M = M_{01} ⊆ Fix(K′)`, so `K′` acts trivially there.
  - The kernel of `A_0 → Aut(S_{X∖U}M)` is a normal subgroup of `A_0` containing `K′ ≠ 1`.
  - `E3_U` is simple: the corner `e_UR_Xe_U` is the crossed product of the induced first-return system `(U,T_U)`, a
    minimal subshift, so Theorem 1 of the note applies. So the kernel is all of `A_0`. ∎

*Import flagged:* the corner `e_U(LC(X,F_2)⋊Z)e_U` is isomorphic to `LC(U,F_2)⋊_{T_U}Z`: the reduction of a free
transformation groupoid to a clopen set is the transformation groupoid of the first-return map, and `T_U` is minimal
and expansive. This is standard and not source-checked here.

## 3. Proposition F: a Boolean realization under two vanishing hypotheses

- **(O) Orthogonality.** `S_V S_W = 0` for all disjoint clopen `V, W ⊆ X`.
- **(O′) No constant fixed vectors.** `S_X = I`, that is, `Fix(α(F21_X)) = 0`.

**Proposition F.** Assume (O) and (O′). Then:
1. `V ↦ S_V` is an injective unital Boolean algebra homomorphism `Clopen(X) → Idem(M_3(R_Y))` with commuting values:
   `S_{V⊔W} = S_V + S_W` for disjoint `V, W`, `S_{V∩W} = S_VS_W`, and `S_{X∖V} = I − S_V`.
   So `𝔅 := span_{F_2}{S_V} ≅ LC(X,F_2)` is a commutative Boolean subalgebra of `M_3(R_Y)`.
2. For every clopen `V`, `α(E3_V) ≤ G_Y ∩ (I + S_V M_3(R_Y) S_V)`.
3. `α(L_X) ≤ C_{G_Y}(𝔅)`.

*Proof.*
1. *Additivity.* Let `V ∩ W = ∅` and `K_V = α(F21_V)`, `K_W = α(F21_W)`.
   - By (O) the joint piece where both act without fixed vectors is `S_VS_WM = 0`, so
     `M = Fix(K_V×K_W) ⊕ (S_V(I−S_W)M) ⊕ ((I−S_V)S_WM)`.
   - `α(F21_{V⊔W})` is the diagonal `{α(q_V)α(q_W)}`. On the second piece it acts as `K_V` (fixed-point free), and on
     the third as `K_W`. So `Fix(α(F21_{V⊔W})) = Fix(K_V) ∩ Fix(K_W)`, which gives
     `I − S_{V⊔W} = (I−S_V)(I−S_W) = I − S_V − S_W`.
   - *Complements.* With (O′), `I = S_X = S_V + S_{X∖V}`.
   - *Meets.* Write `V = (V∩W) ⊔ (V∖W)` and `W = (V∩W) ⊔ (W∖V)`. Expanding the product and using (O) on the three
     disjoint pairs gives `S_VS_W = S_{V∩W}`.
   - *Injectivity.* By Lemma S(c).
2. By (O) for `(V, X∖V)`, `S_VS_{X∖V} = 0`, so Lemma D (with `U = V`) makes `α(E3_V)` trivial on
   `S_{X∖V}M = (I − S_V)M`.
   - It also preserves `S_VM`, so for `g ∈ α(E3_V)`, `(g−I)(I−S_V) = 0` and `(I−S_V)(g−I) = 0`.
   - So `g − I = S_V(g−I)S_V`.
3. `L_X = L_V × L_{X∖V}` with `L_V ≤ E3_V` and `L_{X∖V} ≤ E3_{X∖V}`.
   - An element `h_1` of `α(L_V)` has the form `I + S_V(·)S_V` by item 2, so it commutes with `S_V`.
   - An element `h_2` of `α(L_{X∖V})` has the form `I + S_{X∖V}(·)S_{X∖V}`, so it commutes with `S_{X∖V} = I − S_V`.
   - So `α(L_X)` commutes with every `S_V`. ∎

**Model tests.**
- *X = Y, α = id:* `S_V = e_V I`, and (O), (O′) hold.
- *α = inn(d), d = diag(u,1,1):* `S_V = d(e_VI)d^{-1} = diag(ue_Vu^{-1}, e_V, e_V) = diag(e_{TV}, e_V, e_V)`.
  - This is a NON-scalar idempotent, while (O) and (O′) still hold.
  - So Proposition F does not claim scalar supports, which is right, since the target is conjugacy by `N_Y`, not by
    `G_Y`.
- *Natural ⊕ trivial fake* (the `H` of sk-diagonal-recognition §4, inside a Morita copy of `M_4`): it has a common fixed
  vector, so (O′) fails. That is consistent with (H2) failing there.

## 4. What remains for (Rec′)

- **(O) and (O′).** Where the X-side proof fails to transport: (O) is a ring identity `(α(g)−I)(α(k)−I) = 0` for
  commuting `g`, `k`, not a group identity.
  - Attempt 1, swapping symmetries: `γ ∈ [[T]]′` with `γ(V) = W` gives `z ∈ G_X` conjugating `F21_V` to `F21_W`. Then
    `α(z)` swaps the pieces `M_{10}` and `M_{01}` and preserves `M_{11}`. That forces nothing.
  - Attempt 2, the (H2) trivial centralizer against a nonzero `Fix(α(F21_X))`: the natural centralizing candidates
    `I + xφ` commute with `α(L_X)`, but membership in `E_3(R_Y)` needs a `K_1`-injectivity input (`sr ≤ 2`, OPEN).
- **(A2): from item 3 to (Rec′).**
  - `C_{M_3(R_Y)}(𝔅)` is an algebra over the central `𝔅 ≅ LC(X,F_2)`, and by item 2 each `α(E3_V)` lives in its
    `S_V`-corner.
  - Next: show that the commutant has pointwise type `M_3(F_2)`, using local finiteness of `α(L_X) ≅ LC(X,Q)`; build
    matrix units `f_ij`; use `K_0(R_Y)` torsion-free and internal cancellation (sk-algebraic-putnam, PASS) to get
    `k ∈ GL_3(R_Y)` with `kE_ijk^{-1} = f_ij`. Then `k ∈ N_Y` or its replacement in Theorem R′.
- **Block-theory input still to check.** `Ext^1_{F_2GL_3(2)}(3,3) = 0`, for the pointwise module structure.
