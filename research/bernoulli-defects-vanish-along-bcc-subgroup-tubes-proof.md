---
rg: 2
id: bernoulli-defects-vanish-along-bcc-subgroup-tubes-proof
kind: route
title: Restrict regular representations at tube-supported configurations to the tube, then apply the anatomy of the Bernoulli comparison for the subgroup
target: bernoulli-defects-vanish-along-bcc-subgroup-tubes
requires:
  - bernoulli-assembly-injective-beyond-the-host
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
  - bernoulli-shift-weak-k-equivalence-and-going-down
artifacts:
  - research/artifacts/bc-bernoulli-subgroup-restriction-2026-09-13.md
---

The complete argument is in `research/artifacts/bc-bernoulli-subgroup-restriction-2026-09-13.md`.

1. **Localization (Lemma 1).** Use the right-regular convention, in which `π_x(f u_g) δ_k = f(g k^(-1)·x) δ_(k g^(-1))`.
   Take a finite-propagation element `a` whose coefficients depend on the coordinates in `W` and whose group support is
   `E`. For `x` supported in `HF`, `π_x(a)` is supported on `l^2(HF')` with `F' = F W^(-1) (E ∪ {e})`, and right
   multiplication preserves unions of right `H`-cosets.
2. **Covariance (Lemma 2).** `π_(h·x)(a) = λ_h π_x(a) λ_h^*` for `h ∈ H`.
3. **Restriction homomorphism (Proposition 3).**
   - Decompose `HF' = ⊔ H c_i`. The entries of `π_x(f u_g)` are the regular representations at `x` of `φ_i u_η`, where
     `η = c_i g c_j^(-1) ∈ H` and `φ_i = f(c_i^(-1)·)`.
   - Faithfulness of the regular representations of the reduced `H`-crossed product makes `Res` a well-defined,
     contractive *-homomorphism on the dense subalgebra.
   - It extends to `I_1 ⋊_r G -> K ⊗ (C_0(X_Y \ {0}) ⋊_r H)`.
4. **Ranks and cylinders (Proposition 4).**
   - Ranks at configurations supported in `Y` are preserved.
   - `[1_(C_s)]` goes to `Σ [1_(C_(c·s))]` over the finitely many right cosets `Hc` with `c F_s ⊆ Y`.
5. **Theorem 5.** Suppose `T_r^(H,Y)` is surjective, which is CEKN Theorem 2.8, second sentence, when `H` satisfies
   Baum--Connes with coefficients (`bernoulli-shift-weak-k-equivalence-and-going-down`).
   - `K_1` of the target vanishes.
   - Each `Res(y)` is `T_r^(H,Y)(m)` for a finitely supported `m`.
   - Rank preservation, together with the Möbius formula of `bernoulli-assembly-injective-beyond-the-host` (item 3),
     gives `n_t(y) = m_([t]_H)` for patterns `t ⊆ Y`.
   - If all ranks vanish, then `m = 0`.
6. **Corollary 6.**
   - A `G`-orbit of patterns meets `X_(HF)` in finitely many `H`-orbits, because `g F_t ⊆ HF` forces `g ∈ HF f^(-1)`.
   - So shape-(a) coefficients escape every good tube, and shapes (b) and (c) restrict to zero there.
