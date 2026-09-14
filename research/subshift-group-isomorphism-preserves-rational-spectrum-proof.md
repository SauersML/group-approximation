---
rg: 2
id: subshift-group-isomorphism-preserves-rational-spectrum-proof
kind: route
title: A cyclic factor makes the group of rank 3m, rank-four type rigidity puts 3m in Div, and prime-twisted periodic models of the other subshift avoid it
target: subshift-group-isomorphism-preserves-rational-spectrum
requires: [tower-subshift-elementary-group-is-el-3k-of-base, cyclic-factor-subshift-el-2-is-simple-kazhdan-lef, el-rank-four-finite-simple-shadows-are-ring-models, rank-four-subshift-groups-see-rational-spectrum, subshift-group-model-sizes-see-rational-spectrum]
artifacts:
  - research/artifacts/sk-rank3-shadows-2026-09-14.md
---

Full proof: artifact §2. By symmetry, show `Cyc(Y) ⊆ Cyc(X)`. Fix `m ≥ 2` in `Cyc(Y)`.
1. **Rank nm.**
   - Lemma C1 gives a continuous `f: Y → Z/m` with `f∘T = f+1`.
   - `U = f^(−1)(0)` satisfies `Y = ⊔_(i<m) T^iU` and `T^mU = U`.
   - The tower and cyclic-factor nodes give `R_Y ≅ M_m(R_(Y_1))` with `Y_1` an infinite minimal subshift, and
     `EL_n(R_Y) = EL_(nm)(R_(Y_1))`, `nm ≥ 6`.
2. **nm ∈ Div.** Theorem E with `N = nm` and `1 ∈ Cyc(Y_1)`.
3. **Transport.** `Div` is an isomorphism invariant (Theorem E), so `nm ∈ Div(EL_n(R_X))`.
4. **Contradiction if m ∉ Cyc(X).**
   - By Lemma C1(a),(b), `m ∤ g_r(X)` for all `r`.
   - Take `N_k = g_(r_k) p_k` with `r_k → ∞` and primes `p_k > m`, `p_k → ∞`. Every `c ∈ Cyc(X)` eventually divides `N_k`.
   - So Theorem C(2) and the degree argument of Corollary C2 (valid in every rank) give
     `(SL_(nN_k)(F_2), elementary markings) → EL_n(R_X)`.
   - `nm | nN_k` would force `m | g_(r_k)`. So `nm ∉ Div(EL_n(R_X))`, a contradiction. ∎

Model tests (artifact §2): Thue–Morse against Sturmian is separated, two Sturmian slopes are not, and `X = Y`
is consistent.
