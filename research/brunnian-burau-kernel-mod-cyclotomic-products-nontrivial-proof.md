---
rg: 2
id: brunnian-burau-kernel-mod-cyclotomic-products-nontrivial-proof
kind: route
title: "Iterated commutators with powers of the three-strand full twist multiply the congruence modulus by (t^{3k}-1)/Phi_3, and centralizers in the free point-pushing group keep them nontrivial"
target: brunnian-burau-kernel-mod-cyclotomic-products-nontrivial
requires:
  - brunnian-four-braids-are-pseudo-anosov
artifacts:
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.py
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.log
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Throughout, `T_k = Δ_3^{2k} = (σ_1σ_2)^{3k} ∈ B_4`, `z = A_{14}A_{24}A_{34}`, and
`Q_k = (t^{3k} − 1)/Φ_3 = ∏_{d | 3k, d ≠ 3} Φ_d ∈ Z[t]`.

1. **Full-twist powers.** Put `P = (ρ_4(T_1) − I)/(t³ − 1)`.
   - Checks 1 of `cyclotomic_jets.py` (exact, sympy) show that `P² = P` and that `Φ_3 P` has
     entries in `Z[t^{±1}]`.
   - From `P² = P`, `(I + aP)^k = I + ((1 + a)^k − 1)P`, so `ρ_4(T_k) = I + (t^{3k} − 1)P` for all
     `k ≥ 1`. The script also confirms this directly for `k = 1..6`.
   - Hence `ρ_4(T_k) − I = Q_k · (Φ_3 P) ≡ 0 mod Q_k`.
   - For `d ≠ 3`, `d | 3d`, so `Φ_d | Q_d`.
2. **Commutator congruence.** If `A ≡ I mod 𝔞` and `B ≡ I mod 𝔟` over `Z[t^{±1}]`, then
   `[A, B] ≡ I mod 𝔞𝔟`.
   - Write `A = I + a` and `B = I + b`.
   - Then `ABA^{-1}B^{-1} − I = (ab − ba)A^{-1}B^{-1}`, which has entries in `𝔞𝔟` because
     `A^{-1}` and `B^{-1}` are integral.
3. **Base.** Let `b = [A_{14}, [A_{24}, A_{34}]]`.
   - `b` is Brunnian and nontrivial (`brunnian-four-braids-are-pseudo-anosov`, Part 1).
   - Pure braids have `ρ_4 ≡ I mod (t − 1)`, since `ρ_4` at `t = 1` is the permutation
     representation. Check 3 of the script confirms this for `b`.
4. **Induction.** List the factors of `F` with multiplicity as `Φ_{d_1}, ..., Φ_{d_m}`, where
   `d_i ≠ 3`. Put `X_0 = b` and `X_i = [T_{d_i}, X_{i−1}]`.
   - *Brunnian.* `Brun_4` is normal in `B_4` (`brunnian-four-braids-are-pseudo-anosov`, Part 1),
     so `T X T^{-1} X^{-1} ∈ Brun_4` whenever `X ∈ Brun_4`.
   - *Congruence.* By steps 1–2, `ρ_4(X_i) ≡ I mod (t − 1) Q_{d_1} ⋯ Q_{d_i}`, and this modulus
     is divisible by `(t − 1) Φ_{d_1} ⋯ Φ_{d_i}`.
   - *Nontrivial.* Suppose `X ∈ Brun_4 \ {1}` and `[T_k, X] = 1`.
     - `Δ_4² = Δ_3² z` in `B_4`. Check 2 verifies this on the faithful Artin action in all
       conventions. `Δ_4²` is central, so `Δ_3²` commutes with `z`, and `T_k = Δ_4^{2k} z^{-k}`.
       Hence `X` commutes with `z^k`.
     - `X` and `z` lie in `K_4 = ker(P_4 → P_3)`: deleting `p_4` from `z = Δ_3^{-2}Δ_4²` gives
       `1`. `K_4` is free (Birman exact sequence, as in `brunnian-four-braids-are-pseudo-anosov`,
       Part 1).
     - In a free group the centralizer of a nontrivial element is infinite cyclic. This is
       classical (Magnus–Karrass–Solitar, *Combinatorial Group Theory*, §2.3 / Lyndon–Schupp,
       Ch. I.2), locator not re-checked, and the graph already uses it
       (`fpbs-torsion-free-tarski-monster-no-amenable-wq-normal-proof`).
     - So `z = u^p` and `X = u^q` for some `u ∈ K_4`.
     - Delete `p_1`. The image of `z = Δ_3^{-2}Δ_4²` is `Δ_2^{-2}Δ_3² = σ_1^{-2}(σ_1σ_2)³`, whose
       exponent sum is `4 ≠ 0`. So `ū ≠ 1`, and `ū` has infinite order because `B_3` is
       torsion-free.
     - `X` is Brunnian, so `ū^q = X̄ = 1`, hence `q = 0` and `X = 1`, a contradiction.

     So every `X_i ≠ 1`. Put `X_F = X_m`, or `X_F = b` when `m = 0`.

   Script checks 4–5 confirm, independently of this argument, that
   `X_2 = [Δ_3^4, Φ_0]` (length 216, `ρ ≠ I`, `≡ I mod (t−1)Q_2²`) and `[Δ_3^{10}, Φ_0]`
   (length 252, `ρ ≠ I`, `≡ I mod (t−1)Q_2Q_5`) behave as predicted. Here `Φ_0 = [T_2, b]` is the
   braid of `burau-minus-one-kernel-meets-brunnian-four-braids`.
5. **Moody consequence.**
   - `𝔞 = (F·(t−1))` satisfies `𝔞(t^{-1}) = 𝔞`: every `Φ_d` is palindromic up to sign and a power
     of `t`.
   - `{g : ρ_4(g) ≡ I mod 𝔞}` is a normal subgroup, so every conjugate `Φ_0` of `X_F^k` satisfies
     `ρ_4(Φ_0) ≡ I mod 𝔞`, and `ρ_5(f(Φ_0)) = ρ_4(Φ_0) ⊕ 1 ≡ I mod 𝔞`.
   - Theorem A of the artifact (§5, for any `Γ ∈ B_5` and both orders) and Lemma 3.1 give
     `(1 − t^s)(𝕄_{f(Φ_0)Γ} − 𝕄_Γ) ∈ (F·(t−1))`.
   - `1 − t^{±1}` is a unit times `t − 1`, and `Z[t^{±1}]` is a UFD, so the difference lies in
     `(F)`. ∎

**Where the method stops.**
- `Φ_3` is the one excluded factor: `ρ_4(T_k)` is not `≡ I mod Φ_3`, and check 6 shows
  `ρ_4(Φ_0) ≢ I mod Φ_3`.
- Whether some nontrivial Brunnian braid has `ρ_4 ≡ I mod Φ_3`, that is `ρ_4(X)(ω) = I` at a
  primitive cube root of unity, is not settled here.
