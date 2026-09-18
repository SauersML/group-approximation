---
rg: 2
id: rf-toeplitz-subshifts-from-normal-chains-are-free
kind: claim
title: The residually finite Toeplitz subshift built from a normal chain is free at every point, not only topologically free
requires:
  - rf-toeplitz-subshifts-over-residually-finite-groups
distinct_from:
  rf-toeplitz-subshifts-over-residually-finite-groups: that proves minimality, residual finiteness and a free dense orbit (topological freeness); this upgrades the same subshift to freeness at every point, using only the one-hole-coset structure, normality of the chain and minimality.
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) for all infinite fp groups with solvable word problem; this gives freeness for the Toeplitz construction, which only exists over residually finite groups.
---

**ESTABLISHED (lane proof, bh-g1-effective, 2026-09-18; not independently reviewed).**

**Setting.** Let `Γ` be finitely generated, infinite and residually finite, and let
`X_Γ ⊆ {0,1}^Γ` be the orbit closure of the Toeplitz array `x` of
`rf-toeplitz-subshifts-over-residually-finite-groups`. It is built from a chain of
finite-index **normal** subgroups `Γ_1 ≥ Γ_2 ≥ …` with `∩_m Γ_m = {1}`. The action is
`(λ·z)(μ) = z(μλ)`. The two properties of the construction used here are:
- (F1) at level `m`, `x` is constant on every `Γ_m`-coset except the hole coset `C_m`;
- (M) `X_Γ` is minimal and infinite.

Both are recorded on that node, whose route has two PASS reviews.

**Theorem.** `Γ` acts freely on `X_Γ`: if `z ∈ X_Γ`, `λ ∈ Γ` and `λ·z = z`, then `λ = 1`.

**Proof.**
1. *Every point has at most one non-constant `Γ_m`-coset.* Write `z = lim_k γ_k·x`.
   - Since `[Γ:Γ_m] < ∞`, pass to a subsequence along which the coset `γ_kΓ_m =: c` is
     constant.
   - For a coset `νΓ_m`, normality gives `νΓ_m γ_k = νγ_kΓ_m`. So `γ_k·x` restricted to
     `νΓ_m` is `x` restricted to `νγ_kΓ_m`, read through right translation by `γ_k`.
   - By (F1) that restriction is constant unless `νγ_kΓ_m = C_m`, i.e. unless
     `νΓ_m = E_m := C_m c^{-1}`. The constant value is `x` on the coset `νcΓ_m`, which is
     independent of `k`.
   - Passing to the limit, `z` is constant on every `Γ_m`-coset other than `E_m`.
2. *Exactly one.* If `z` were also constant on `E_m`, then `z` would be constant on every
   `Γ_m`-coset. That makes `z` fixed by `Γ_m` (normality), so its orbit has at most
   `[Γ:Γ_m]` points. That orbit is closed and invariant, so by (M) it equals `X_Γ`, which is
   then finite. This contradicts (M). So `E_m` is the unique `Γ_m`-coset on which `z` is not
   constant.
3. *Stabilizers lie in every `Γ_m`.* If `λ·z = z`, the non-constant cosets of `λ·z` are the
   cosets `νΓ_m` with `νλ ∈ E_m`, i.e. the coset `E_mλ^{-1}`. Uniqueness in step 2 gives
   `E_mλ^{-1} = E_m`. For a coset `E_m = eΓ_m` of a normal subgroup this means
   `eλ^{-1}e^{-1} ∈ Γ_m`, i.e. `λ ∈ Γ_m`.
4. This holds for every `m`, so `λ ∈ ∩_m Γ_m = {1}`. ∎

**Remarks.**
- The index bound `d_m ≥ max(m+2, 2|B_(m-1)|+1)` of the construction is not used, and
  neither is the RF (Kerr–Nowak) part.
- Normality is used in steps 1 and 3. For a non-normal chain the associated odometer can have
  nontrivial stabilizers, and step 3 fails.

**Consequence.** With the decidable-language node this gives (M2) for every effectively
residually finite group with solvable word problem, and in particular for every infinite
finitely presented residually finite group and every infinite finitely generated linear group.
See `effectively-rf-groups-have-effective-minimal-free-subshifts`.

**Lesson for general BH.** Finite quotients give free minimal effective dynamics almost for
free: one aperiodic coset per level, plus normality, pins every stabilizer into every
`Γ_m`. The inputs Boone–Higman reduces to are infinite simple groups (with the
Kazhdan and FA properties), which have no finite quotients. So for them this profinite
mechanism is not merely unproved but unavailable, and the (M2) gate is exactly the
problem of finding free minimal effective dynamics without a profinite skeleton.
