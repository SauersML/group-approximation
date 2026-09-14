---
rg: 2
id: local-annihilation-el-simplicity-explicit-extraction
kind: route
title: Two explicit commutators turn a locally annihilated noncentral commutator into a nontrivial root
target: local-annihilation-makes-projective-el-simple
requires: []
artifacts:
  - research/artifacts/sk-general-master-2026-09-13.md
  - research/artifacts/sk-general-master-proposal-2026-09-13.md
---

Direct paper proof, with every identity written out. The route
`local-annihilation-makes-projective-el-simple-proof` states step 3 only as "column extraction". This version is
the one proposed for the note.
- Lane: sk-general-master, 2026-09-13.
- Status: UNREVIEWED, queued with sk-referee-1.

**Setting.** Let `R` be a unital simple ring and `n ≥ 3`. Assume local annihilation: for every finite `F ⊆ R`, the set
`S_F = {s : ∃ t ≠ 0 with ts = 0 and tfs = 0 for all f ∈ F}` generates `R` as a non-unital ring. Let `N ⊴ EL_n(R)`
contain a noncentral `g`. Write `E_pq` for matrix units, `e_pq(r) = I + rE_pq`, and `[x,y] = xyx⁻¹y⁻¹`.

1. **A noncommuting annihilated root.** Let `F` be the set of entries of `g`. Put
   `C_g = {s : [g, e_ij(s)] = 1 for all i ≠ j}`. It is a non-unital subring:
   - `e_ij(r+s) = e_ij(r)e_ij(s)`;
   - `e_ij(rs) = [e_ik(r), e_kj(s)]` for `k ∉ {i,j}`.
   `C_g ≠ R`: the `e_ij(r)` generate `EL_n(R)` and `g` is not central. So some `s ∈ S_F`, with its `t`, and some
   `i ≠ j` give `ρ = [g, h] ≠ 1` for `h = e_ij(s)`. `ρ ∈ N`.

2. **`t` kills `ρ − I`.** We have `ρ − I = (g·sE_ij·g⁻¹)·e_ij(−s) − sE_ij`.
   - The `(p,q)` entry of the first term is `g_pi · s · (g⁻¹e_ij(−s))_jq`.
   - The second term has the single entry `−s`.
   So `t(ρ − I) = 0` entrywise, by `tg_pi s = 0` and `ts = 0`.

3. **A one-column matrix in `N`.**
   - Put `Y = ρ⁻¹ − I ≠ 0`, pick `Y_qm ≠ 0`, and pick `l ∉ {m, q}`.
   - A simple ring is prime, so `Y_qm R t ≠ 0`. Pick `c` with `z = Y_qm c t ≠ 0`.
   - Row `m` of `ctE_ml·ρ` is `ct` times row `l` of `ρ`, and `t(ρ−I) = 0`. So `ctE_ml·ρ = ctE_ml`, that is,
     `e_ml(ct)ρ = ρ + ctE_ml`.
   - Then `v := ρ⁻¹ e_ml(ct) ρ e_ml(−ct) = (I + ρ⁻¹ctE_ml)(I − ctE_ml) = I + Y·ctE_ml`, because
     `E_ml·ctE_ml = 0` (`l ≠ m`).
   - `v ∈ N`. `v` differs from `I` only in column `l`, and `v_ql = z` (`q ≠ l`).

4. **Its inverse.** If `Mv = I`, then `Me_k = Mve_k = e_k` for `k ≠ l`. So `v⁻¹` also differs from `I` only in column
   `l`. Comparing `(l,l)` entries of `v⁻¹v = I` and `vv⁻¹ = I` gives `(v⁻¹)_ll v_ll = 1 = v_ll (v⁻¹)_ll`. So `(v⁻¹)_ll`
   is a unit.

5. **A root.** Take `b ∉ {l, q}` and `B = e_bq(1)`. Let `ω` be column `l` of `v − I`, so `v = I + ωe_l^T`.
   - `Bv − vB = E_bq ω e_l^T − ω e_l^T E_bq = ω_q E_bl = zE_bl`, since `e_l^T E_bq = 0` for `b ≠ l`.
   - So `[B, v] = (vB + zE_bl)B⁻¹v⁻¹ = I + zE_bl·v⁻¹`, because `E_bl B⁻¹ = E_bl` for `l ≠ b`.
   - Row `l` of `v⁻¹` is `(v⁻¹)_ll e_l^T`. So `[B, v] = e_bl(z(v⁻¹)_ll)`.
   - `z(v⁻¹)_ll ≠ 0`, so `N` contains a nontrivial root.

6. **The level ideal.** `J = {r : e_pq(r) ∈ N for all p ≠ q}` is additively closed, and two-sided by
   `e_pq(ar) = [e_pk(a), e_kq(r)]` and `e_pq(ra) = [e_pk(r), e_kq(a)]`. Signed permutation matrices lie in `EL_n(R)`,
   and they conjugate `e_bl(r)` to `e_pq(±r)`, so `z(v⁻¹)_ll ∈ J`. `R` is simple, so `J = R` and `N = EL_n(R)`.

**Centre.** A central element commutes with every `e_ij(1)`, so it equals `λI`. Commuting with every `e_ij(a)` gives
`λ ∈ Z(R)^×`.

**Additive variant.** Suppose `S_F` additively spans `R`. This holds for Steinberg algebras
(`steinberg-algebras-have-local-annihilation`) and for `LC(X,F_q) ⋊ Z` directly. Then step 1 uses only
`e_ij(r+s) = e_ij(r)e_ij(s)`. This is the form in the note proposal.

**Credit.** The extraction follows Stepanov's Lemma 4.3 (`stepanov-linear-dependence-standard-normal-structure`, as
recorded in `research/artifacts/un-stepanov-credit-2026-09-13.md`). Lane sk-citations verifies the lemma number
against the source.
