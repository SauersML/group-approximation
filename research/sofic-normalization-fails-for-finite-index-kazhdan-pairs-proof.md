---
rg: 2
id: sofic-normalization-fails-for-finite-index-kazhdan-pairs-proof
kind: route
title: Read the failure off the lamp at the compressed coset, and close the centralizer under Kun--Thom one pair at a time
target: sofic-normalization-fails-for-finite-index-kazhdan-pairs
requires:
  - sofic-non-mf-witness
  - sofic-groups-kill-rigid-compression-defects
  - compression-defects-grow-under-centralizer-closure
---

Commutators are `[x,y] = x y x^-1 y^-1`. Affine pairs `(v, A)` act by `x -> A x + v`, so
`(v,A)(w,B) = (v + A w, A B)` and `(v,A)^-1 = (-A^-1 v, A^-1)`. `E_ij` is the elementary matrix
`I + e_i e_j^T` (`i != j`).

## Step 1: (F1)

- **(T).** `Gamma = Z^3 ⋊ SL_3(Z)` has property (T) [BHV, Example 1.7.4(i)], and
  `Gamma' = alpha(Gamma) ≅ Gamma` because `alpha` is injective.
- **Index.** `Gamma' = {(w, A) : w in 2Z^3}`, so `Gamma/Gamma' ≅ Z^3/2Z^3` as sets, and the index
  is 8.
- **Conjugation formula.** For `g = (v, B)` and `h = (w, A)`,
  ```text
  g h g^-1 = ( B w + (I - B A B^-1) v ,  B A B^-1 ).                                   (C)
  ```
- **Normal closure.** `(0, A) in Gamma'`. By (C) with `g = (e_j, I)`,
  `(e_j,I)(0,A)(e_j,I)^-1 (0,A)^-1 = ((I - A) e_j, I)`. Take `A = E_ij^-1 = I - e_i e_j^T`. Then
  `(I - A) e_j = e_i`. So `<<Gamma'>>^Gamma` contains every translation `e_i` and all of
  `SL_3(Z)`, hence equals `Gamma`.
- **Compressors.** Let `g = (v, B)` with `g Gamma' g^-1 <= Gamma'`. By (C), with `w = 0`,
  `(I - A') v in 2Z^3` for every `A' = B A B^-1`, that is, for every `A' in SL_3(Z)`. If some
  coordinate `v_i` is odd, `A' = E_ji` (`j != i`) gives `(I - A') v = -v_i e_j`, which is not in
  `2Z^3`. So `v in 2Z^3` and `g in Gamma'`. Conversely `Gamma'` compresses itself. So
  `Comp_Gamma(Gamma') = Gamma'`, which generates `Gamma' != Gamma`.

## Step 2: the witness and (F2)

From `non_mf_groups_exist.tex` (display `eq:affine-clifford-witness` and the paragraph before
it), with `Gamma`, `alpha` and `a = (e_1, I)` as the manuscript's concrete instance:
- `V = T_alpha ⋊ <t>`, with `t g t^-1 = alpha(g)` on the level-zero copy of `Gamma`, and
  `T_alpha = ⋃_(n >= 0) t^-n Gamma t^n`.
- `X = V/Gamma`. `Cl(X) ≅ F_2 x F_2^(X)`, with the twisted law, `c_x -> (0, delta_x)`, and
  `ε -> (1, 0)`. So the `c_x` are pairwise distinct, `c_x c_y != 1` for `x != y`, and
  `ε != 1`.
- `V` acts by `g c_x g^-1 = c_(g x)`, and `W = Cl(X) ⋊ V` is sofic (`sofic-non-mf-witness`).

For `x = g Gamma in X`, `Stab_V(x) = g Gamma g^-1`. So an element `h in V` centralizes `c_x` in
`W` if and only if `h x = x`, that is, `h in g Gamma g^-1`. Put `x_0 = Gamma` and `y = t x_0`.
Then `Stab_V(y) = t Gamma t^-1 = Gamma'`.

- `c_y` centralizes `Gamma'`, since `Gamma' = Stab(y)`.
- `c_y` does not centralize `Gamma`. We have `a in Gamma \ Gamma'`, so `a y != y`, and
  `a c_y a^-1 = c_(a y) != c_y`. Hence `C_W(Gamma') != C_W(Gamma)`.
- `Gamma` does not normalize `C_W(Gamma')`. The element `c_(a y) = a c_y a^-1` centralizes
  `Gamma'` only if `Gamma' <= Stab(a y) = a Gamma' a^-1`, that is, `a^-1 Gamma' a <= Gamma'`. By
  (C) with `g = a^-1 = (-e_1, I)` and `h = (0, E_21)`, the translation part is
  `-(I - E_21) e_1 = e_2`, which is not in `2Z^3`. So `c_(a y) notin C_W(Gamma')`.
- `C_W(<<Gamma'>>^Gamma) = C_W(Gamma)` by Step 1.

## Step 3: (F3)

`W` is countable and sofic, so an injective `σ : W -> S_U` exists (the ultraproduct form of the
definition; see the ladder artifact, property (U)).
- `σ(c_y)` commutes with `σ(Gamma')`.
- By Step 2, some `h in Gamma'` has `[c_(a y), h] != 1`. Injectivity gives
  `[σ(a) σ(c_y) σ(a)^-1, σ(h)] != 1`. So `σ(a) in σ(Gamma)` moves `σ(c_y)` out of
  `C_(S_U)(σ Gamma')`.
- `σ(c_y)` does not commute with `σ(a)`, and `a in Gamma = <<Gamma'>>^Gamma`. So
  `C(σ Gamma') != C(σ <<Gamma'>>^Gamma)`.

## Step 4: (F4)

- Let `Delta <= W` be Kazhdan. Its image under `W -> V -> V/T_alpha ≅ Z` is a Kazhdan subgroup
  of `Z`, hence finite, hence trivial. So `Delta <= Cl(X) ⋊ T_alpha`.
- Its image `Delta-bar` in `T_alpha = (Cl(X) ⋊ T_alpha)/Cl(X)` is finitely generated, since
  `Delta` is.
- `T_alpha` is the union of the chain `t^-n Gamma t^n`. The chain is strictly increasing, since
  `alpha(Gamma) != Gamma`. So every finitely generated subgroup of `T_alpha` lies in one member
  of the chain and is proper.
- If `Delta >= T_alpha`, then `Delta-bar = T_alpha` would be finitely generated, which is a
  contradiction.

## Step 5: (H)

Throughout, `G` is countable and sofic, `L <= G`, and `Z = C_G(L)`.

- **The hull exists.** Call `H <= G` *closed* when `Gamma <= H` Kazhdan, `Delta <= G` Kazhdan
  and `Gamma` infranormal in `Delta` imply `<<Gamma>>^Delta <= H`. `G` is closed, and an
  intersection of closed subgroups is closed. So `Hull_G(L)` is the intersection of all closed
  `H >= L`.
- **`B = C_G(Z)` is closed.** Let `Gamma <= B`, `Delta`, be as above. Then `Z <= C_G(Gamma)`.
  Apply `sofic-groups-kill-rigid-compression-defects` with ambient `H = G` and pair
  `Gamma <= Delta`: for `d in Delta`, `z in Z` and `gamma in Gamma`, `[d^-1 z d, gamma] = 1`.
  Equivalently `z` commutes with `d gamma d^-1`. These elements generate `<<Gamma>>^Delta`, so
  `<<Gamma>>^Delta <= C_G(Z) = B`.
- **Conclusion.** `L <= B`, so `Hull_G(L) <= B`. That is, `Z` centralizes `Hull_G(L)`, so
  `C_G(Hull_G(L)) >= C_G(L)`. The reverse inclusion holds because `L <= Hull_G(L)`.

## Step 6: (HK)

Let `u in Comp_G(L)`, so `u L u^-1 <= L`, and suppose `u^-n L u^n <= Hull_G(L)` with `n >= 1`.
- Conjugating centralizers reverses inclusion: `u^k Z u^-k = C_G(u^k L u^-k)`, and
  `u^(k+1) L u^-(k+1) <= u^k L u^-k`. So `Z <= u Z u^-1 <= ... <= u^n Z u^-n`.
- By (H), `C_G(u^-n L u^n) >= C_G(Hull_G(L)) = Z`, that is, `u^-n Z u^n >= Z`, or
  `u^n Z u^-n <= Z`.
- So the chain is constant, and `u Z u^-1 = Z`. For `c in Z` and `l in L`, `u c u^-1 in Z`
  commutes with `l`, so every generator `[u c u^-1, l]` is trivial.

## Step 7: (HS)

Let `K` be normal and Kazhdan in `G`, with `G/K ≅ Z`, and let `L <= K` with `L = C_K(C_G(L))`.
- **`K` is closed** in the sense of Step 5. A Kazhdan `Delta <= G` maps to a Kazhdan, hence
  finite, hence trivial, subgroup of `Z`, so `Delta <= K`. Then `<<Gamma>>^Delta <= K` for
  every `Gamma <= Delta`.
- **Saturation.** `L <= K`, so `Hull_G(L) <= K`. By (H), `Hull_G(L) <= C_G(C_G(L))`. So
  `Hull_G(L) <= C_G(C_G(L)) ∩ K = C_K(C_G(L)) = L`, and `Hull_G(L) = L`.
- **Normalizing overgroups.** If `L` is Kazhdan and infranormal in a Kazhdan `Delta`, take
  `Gamma = L`: `<<L>>^Delta <= L`, so `Delta` normalizes `L`.
- **Strict compressors.** If `u L u^-1 < L` strictly, conjugating by `u^-1` gives
  `L < u^-1 L u <= u^-n L u^n` for `n >= 1`. So `u^-n L u^n ⊄ L = Hull_G(L)`, and (HK) does not
  apply to any strict compressor of a closed source.

## Step 8: calibration of (HK)

Put `L = Gamma` in `W`, with `c = c_(x_0)`.
- `t Gamma t^-1 = Gamma' <= Gamma`, so `t in Comp_W(Gamma)`. `Gamma = Stab_V(x_0)`, so
  `c in C_W(Gamma)`.
- `t c t^-1 = c_(t x_0) = c_y`. Since `a c_y a^-1 = c_(a y)` and `c_y` is an involution,
  `[t c t^-1, a] = c_y c_(a y)`.
- `a notin Gamma' = Stab(y)`, so `a y != y`. Under the homomorphism of Step 2,
  `c_y c_(a y) -> (B(delta_y, delta_(a y)), delta_y + delta_(a y))`, whose second coordinate is
  nonzero. So `[t c t^-1, a] != 1`.
- By Step 6, applied contrapositively, `t^-n Gamma t^n ⊄ Hull_W(Gamma)` for every `n >= 1`.
