---
rg: 2
id: thompson-f-germ-local-hs-models-almost-commute-proof
kind: route
title: Interior cylinders have many disjoint x_0-translates, so a central state puts the frame on the end germs, where F' acts trivially by locality
target: thompson-f-germ-local-hs-models-almost-commute
requires: []
---

Conventions: `x_0` acts on `X` by `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w`; on `[0,1]` it is `t/2`,
`t − 1/4`, `2t − 1` on `[0,1/2]`, `[1/2,3/4]`, `[3/4,1]`. It is increasing, fixes exactly `0` and `1`,
and satisfies `x_0(t) < t` on `(0,1)`.

1. **Disjoint translates.** Let `C_m = X \ ([0^m] ∪ [1^m])`, the clopen of the dyadic interval
   `K_m = [2^-m, 1 − 2^-m]`. Since `x_0^j(t) → 0` for `t < 1`, there is `L` with
   `x_0^L(1 − 2^-m) < 2^-m`. Applying the increasing map `x_0^(iL)` gives
   `max x_0^((i+1)L) K_m < min x_0^(iL) K_m`. So the intervals `x_0^(iL) K_m`, `0 ≤ i < N`, are
   pairwise disjoint with dyadic endpoints, and the clopens `x_0^(iL) C_m` are pairwise disjoint.
   For `m = 2`: `x_0(3/4) = 1/2`, `x_0(1/2) = 1/4`, `x_0(1/4) = 1/8`, so `L = 3`.
2. **Support.** `c = x_0 x_1 x_0^-1 x_1^-1` fixes `[0,1/4] ∪ [3/4,1]` pointwise
   (`thompson-f-spatial-permutation-models-almost-commute-proof`, step 1), i.e. `[00] ∪ [11]`.
   Every `g ∈ F'` has trivial germs at `0` and `1`, hence fixes `[0^m] ∪ [1^m]` for some `m`.
3. **Mass bound, finitary.** Write `C = C_m` and `h_i = x_0^(iL)`. The frame projections commute and
   the `h_i C` are disjoint, so `Σ_{i<N} P_{h_i C} = P_{∪ h_i C} ≤ 1`, and `Σ_i tr P_{h_i C} ≤ 1`.
   For `i ≥ 1`,
   `|tr P_C − tr P_{h_i C}| = |tr(U_{h_i} P_C U_{h_i}* − P_{h_i C})| ≤ ||·||_2 ≤ η_cov`,
   because `|tr X| ≤ ||X||_2` for the normalized trace. Hence `N tr P_C ≤ 1 + (N−1) η_cov`, and
   `tr P_C ≤ 1/N + η_cov`.
4. **Commutator, finitary.** `1 − P_C = P_{0^m} + P_{1^m}`. Locality gives
   `||(U_g − 1)(1 − P_C)||_2 ≤ 2 η_loc`. Also `||(U_g − 1) P_C||_2 ≤ ||U_g − 1||_op ||P_C||_2 ≤
   2 (tr P_C)^(1/2)`. Adding the two bounds gives `||U_g − 1||_2 ≤ 2η_loc + 2 sqrt(1/N + η_cov)`.
5. **Representations.** With exact covariance, invariance of `Φ` gives `Φ(P_{h_i C}) = Φ(P_C)`, so
   `N Φ(P_C) ≤ 1` for all `N`, and `Φ(P_C) = 0`. Every clopen avoiding `0^∞, 1^∞` lies in some `C_m`.
   Locality gives `π(g)(1 − P_C) = 1 − P_C`, so `Φ(1 − π(g)) = Φ((1 − π(g)) P_C)`. By Cauchy–Schwarz,
   this is at most `Φ((1−π(g))(1−π(g))*)^(1/2) Φ(P_C)^(1/2) = 0`.
6. **Compressions.** Let `Q_n` be almost invariant in normalized HS. Any weak-* cluster point `Φ` of
   `T ↦ Tr(Q_n T)/Tr(Q_n)` is `Ad π(F)`-invariant, since
   `|Tr(Q_n (π(g)Tπ(g)* − T))| ≤ ||T|| · ||π(g)*Q_nπ(g) − Q_n||_1`, and
   `||·||_1 ≤ rank^(1/2) ||·||_2^HS`. This holds for every cluster point, so step 5 applies along the
   whole sequence: `Re tr(Q_n π(c) Q_n) → 1` in normalized trace, and
   `||Q_n(π(c) − 1)Q_n||_2² ≤ tr(Q_n (1−π(c))*(1−π(c)) Q_n) = 2 − 2 Re tr(Q_n π(c) Q_n) → 0`.
   Almost invariance makes the compression of the product close to the product of the compressions,
   so the compressed model's commutator tends to `1`.
7. **Members.**
   - Koopman: `U_g 1_[w] ξ` is supported on `g[w]`, and its formula uses only `g^-1` on the open set
     `g[w]`, i.e. `g|_[w]`.
   - Cuntz: refine the tree pair so that every domain leaf either extends `w` or is disjoint from it.
     Then `π(g) S_w S_w* = Σ_{v_i ⊇ w} S_{u_i} S_{v_i}*` and `π(g) S_v S_v* π(g)* = S_{gv} S_{gv}*`.
   - Pythagorean: the leaf-component description is the same computation with `S_0*, S_1*` replaced
     by `A, B`.
8. **Covariance-only counterexample schema.** This is the tensor argument in the claim's Scope. It
   uses only that `||X ⊗ Y − 1||_2 ≤ ||X − 1||_2 + ||Y − 1||_2` for unitaries, and that
   `||(λ(c) ⊗ σ(c) − 1)(P_w ⊗ 1)||_2 ≥ ||(σ(c) − 1)||_2 (tr P_w)^(1/2) − ||(λ(c) − 1)||_2`.
