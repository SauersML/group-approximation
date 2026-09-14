# sk-rank3-shadows: the rational spectrum is an isomorphism invariant of G_X in rank three (2026-09-14)

Lane sk-rank3-shadows (wave 12). The problem was rank-three finite simple shadows of `G_X = EL_3(LC(X,F_2)⋊Z)` and the rational spectrum of `X` as a group invariant. Main tip at start: e81f21d8c2. Status: established with complete proofs below, UNREVIEWED, queued with sk-verify-18.

## 0. Plan and result
- **Target (b), settled for every n ≥ 3 including the paper's n = 3.** If `EL_n(R_X) ≅ EL_n(R_Y)`, then `X` and `Y` have the same finite cyclic factors, i.e. the same rational continuous eigenvalues.
- **Target (a), settled when X has a finite cyclic factor of order ≥ 2.** Every finite simple approximant of `G_X` is then eventually projective special linear in characteristic 2, induced by ring models. It stays OPEN for totally minimal `X` (Sturmian, Fibonacci).
- **The idea.** Theorem E needed type rigidity for BOTH groups. It is enough to have it for the group that HAS the cyclic factor, and that group is secretly of higher rank. The group LACKING the cyclic factor only needs some approximant sequence of the wrong dimension, and periodic models supply one in every rank.

## 1. Inputs, all on main and reviewed
- **[T] `tower-subshift-elementary-group-is-el-3k-of-base` and `cyclic-factor-subshift-el-2-is-simple-kazhdan-lef`** (PASS, sk-verify-3, sk-verify-5).
  - If `Y` is an infinite minimal subshift and `U ⊆ Y` is clopen with `T^m U = U` and `Y = U ⊔ TU ⊔ … ⊔ T^(m−1)U`, then `Y_1 = (U, T^m|_U)` is conjugate to an infinite minimal subshift.
  - `R_Y ≅ M_m(R_(Y_1))`, with matrix units `u^i e_U u^(−j)`.
  - `EL_n(M_m(S)) = EL_(nm)(S)` for `n ≥ 2`: a transvection inside one block is a commutator through another block.
- **[C1] Lemma C1 of `subshift-group-model-sizes-see-rational-spectrum`** (PASS WITH FIXES, sk-verify-14 part2).
  - `g_r | g_(r+1)`.
  - `m ∈ Cyc(X)` iff there is a continuous `f: X → Z/m` with `f∘T = f+1`, iff `m | g_r` for all large `r`.
- **[C2] Theorem C(2) and the degree argument of Corollary C2** (same node; valid in every rank, as used in Theorem E ⊆).
  - For all large `N ≡ 0 mod g_r` there is a primitive periodic word of length `N` with the `(r+1)`-language of `X`.
  - The resulting ring models give `(SL_(nN_k)(F_2), elementary marking) → (EL_n(R_X), elementary marking)` along any `N_k → ∞` in which every order in `Cyc(X)` eventually divides `N_k`.
- **[D] Theorem D, `el-rank-four-finite-simple-shadows-are-ring-models`** (PASS, sk-verify-14 part7). For `N ≥ 4` and every f.g. ring `R`, every sequence of finite nonabelian simple groups converging to `EL_N(R)` is eventually `PSL_(Nd_k)(F_(q_k))`, with the marking induced by surjective ring maps `ρ_k: F → M_(d_k)(F_(q_k))`, where `F` is free on the generators of `R`. If `EL_N(R)` is infinite simple, `d_k → ∞`.
- **[E] Theorem E, `rank-four-subshift-groups-see-rational-spectrum`** (PASS, sk-verify-14 part7).
  - `Div(G)` is the set of `m` such that every sequence of finite simple groups converging to `G`, for any finite marking, eventually consists of `PSL_(M_k)(F_(q_k))` with `m | M_k`.
  - `Div` is an isomorphism invariant, since changing the marking preserves converging sequences, and the natural dimension `M` of `PSL_M(F_q)` is well defined for large `M`.
  - `Div(EL_N(R_X)) = {m : m | N c, c ∈ Cyc(X)}` for `N ≥ 4`.

## 2. Theorem R (rank-three invariance of the rational spectrum)
**Theorem R.** Let `X, Y` be infinite minimal subshifts and `n ≥ 3`. If `EL_n(LC(X,F_2)⋊Z) ≅ EL_n(LC(Y,F_2)⋊Z)`, then `Cyc(X) = Cyc(Y)`: the two subshifts have the same finite cyclic factors, equivalently the same rational continuous eigenvalues. In particular `G_X ≅ G_Y` forces equal rational spectra.

*Proof.* By symmetry it suffices to show `Cyc(Y) ⊆ Cyc(X)`. Let `m ≥ 2` with `m ∈ Cyc(Y)`.
1. **The group with the factor is of rank nm.**
   - By [C1] there is a continuous `f: Y → Z/m` with `f∘T = f+1`. Put `U = f^(−1)(0)`. Then `T^iU = f^(−1)(i)`, `T^mU = U`, and `Y = U ⊔ TU ⊔ … ⊔ T^(m−1)U`.
   - By [T], `R_Y ≅ M_m(R_(Y_1))` for an infinite minimal subshift `Y_1`, and `G := EL_n(R_Y) = EL_(nm)(R_(Y_1))`, with `nm ≥ 6`.
2. **nm ∈ Div(G).** By [E] with `N = nm ≥ 4` and `c = 1 ∈ Cyc(Y_1)`, every sequence of finite simple groups converging to `G`, for any marking, eventually has natural dimension divisible by `nm`.
3. **Transport.** Let `ψ: EL_n(R_X) → G` be an isomorphism. By invariance of `Div` ([E]), `nm ∈ Div(EL_n(R_X))`.
4. **The group without the factor has approximants of the wrong dimension.** Suppose `m ∉ Cyc(X)`.
   - By [C1], `m ∤ g_r(X)` for every `r`: if `m | g_r`, then `m | g_(r′)` for all `r′ ≥ r` by `g_r | g_(r+1)`, so `m ∈ Cyc(X)`.
   - Choose levels `r_k → ∞` slowly and primes `p_k → ∞` with `p_k > m`, and put `N_k = g_(r_k) p_k`.
   - Every `c ∈ Cyc(X)` divides `g_(r_k)` for large `k`, hence divides `N_k`. So by [C2], `(SL_(nN_k)(F_2), elementary markings) → EL_n(R_X)`.
   - These groups are finite simple, with natural dimension `nN_k`. If `nm | nN_k`, then `m | g_(r_k) p_k`, and since `gcd(m, p_k) = 1`, `m | g_(r_k)`, a contradiction.
   - So `nm ∤ nN_k` for every `k`, and `nm ∉ Div(EL_n(R_X))`, contradicting step 3.
5. Hence `m ∈ Cyc(X)`. ∎

**Model tests.**
- *Thue–Morse vs Sturmian.* `Cyc(TM)` contains all `2^j`, and `Cyc(Sturmian) = {1}`. So `G_TM ≇ G_Sturmian`; this was known only in rank ≥ 4 before.
- *Two Sturmian slopes.* Both spectra are `{1}`, so there is no conclusion. This is consistent with `sturmian-elementary-group-lef-growth-is-exp-r-squared`.
- *X = Y.* Trivially consistent.
- *Where each hypothesis enters.* Minimality gives the partition from `f` and a minimal `Y_1`. Infiniteness makes `EL_(nm)(R_(Y_1))` infinite simple, which [D] uses. `F_2` gives `SL = PSL`, the coefficients of [C2], and characteristic 2 in [E]. `n ≥ 3` is needed only for `nm ≥ 4` when `m = 2`; `n = 2` would also give `nm = 4`, but [C2] and [E] are stated for `n ≥ 3`.

**Scope and relation to the paper's Question.**
- The rational spectrum is a strong orbit equivalence invariant (divisibility of the order unit in `K^0(X,T)`; recalled, not checked at source). So Theorem R proves, for the paper's `G_X` itself, a necessary condition that SOE rigidity would imply.
- It does not separate totally minimal subshifts. Whether `G_X ≅ G_Y` implies SOE stays open (`subshift-elementary-group-isomorphism-forces-orbit-equivalence`).

## 3. Corollary S (rank-three type rigidity with a cyclic factor)
**Corollary S.** Let `X` be an infinite minimal subshift with a finite cyclic factor of order `m ≥ 2`, and let `(Q_k, T_k) → (G_X, T)` for some finite marking `T`, with `Q_k` finite simple. Then for all large `k`, `Q_k ≅ PSL_(3md_k)(F_(2^(f_k)))` with `d_k → ∞`, and the marking is induced (after rewriting `T` into the elementary marking of `EL_(3m)(R_(X_1))`) by a surjective ring map `ρ_k: F_1 → M_(d_k)(F_(2^(f_k)))`, where `F_1` is free on generators of `R_(X_1)` and `X_1` is the induced subshift on a cyclic piece. Moreover `3m·c | 3md_k` for every `c ∈ Cyc(X_1)`, i.e. the natural dimensions are divisible by `3·lcm` of the orders in `Cyc(X)` visible at bounded level.

*Proof.* Step 1 of Theorem R gives `G_X = EL_(3m)(R_(X_1))`. A change of marking preserves converging sequences ([E]), so [D] with `N = 3m ≥ 6` applies. `EL_(3m)(R_(X_1))` is infinite and simple, so `d_k → ∞`. The characteristic is 2 because `2 ∈ ker(F_1 → R_(X_1))` is killed eventually ([D](6)). The divisibility is [E] ⊇ for `X_1`, since `Cyc(X) = m·Cyc(X_1)` as supernatural data when `X` is the height-`m` tower over `X_1`. ∎
- So `subshift-group-finite-simple-shadows-are-ring-models` holds for every `X` with a nontrivial finite cyclic factor, including Thue–Morse, period doubling and every Toeplitz subshift.
- It stays open exactly for totally minimal `X`.

## 4. What stays open, and the sharpest next target
- **(a) for totally minimal X.** The only failing input is step 1 of [D] in rank 3 (Krstić–McCool, Corollary 2).
  - Minimal Cantor systems have constant-height towers only for rational eigenvalues. The corner copies `EL_(3h)(e_V R e_V)` inside `G_X`, for small `V` with towers of height ≥ h, do satisfy the finitely presented Steinberg relations of rank `3h ≥ 4` in large approximants. But gluing their ring-type subgroups into a global ring model of `R_X` is a local-to-global problem that no import settles.
  - **Sharpest target:** show that if a finite simple `Q_k` contains, for every clopen piece of a fixed partition, a ring-type `PSL_(3hd)` subgroup matching the corner, then `Q_k` is ring type. One lane at most.
- **(b) beyond the rational spectrum.** Irrational eigenvalues and the full dimension group are invisible to natural dimensions. They need different invariants, such as rank functions (sk-free-6) or characters.

## 5. Novelty and credit (bounded)
- A grep of main finds no rank-three statement. The rank ≥ 4 version is `rank-four-subshift-groups-see-rational-spectrum` (sk-free-4).
- No literature search beyond the imports. The inputs are Krstić–McCool (through EJZ), Voronetsky (central `K_2`), and the classification uniqueness of natural dimensions for large rank, all as imported by [D] and [E].
- For the paper, a remark would need the proof of [D], about half a page, so this is proposed as a Cairn result only. Main's call.
