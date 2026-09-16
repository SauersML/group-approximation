---
rg: 2
id: burau-minus-one-kernel-meets-brunnian-four-braids-proof
kind: route
title: "Commutator of the squared three-strand full twist with a basic Brunnian commutator"
target: burau-minus-one-kernel-meets-brunnian-four-braids
requires: []
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Full proof: artifact §8, Proposition 8.1.
Certificate: `experiments/zp-burau-parity-t-minus-one-2026-09-16/burau_minus_one.py`, run under
`timeout 600`. It uses exact integer Laurent polynomials, exits 0, and its log is `run.log`.

1. **`b ∈ Brun_4`.** `Brun_4` is the intersection of the kernels of the strand-forgetting maps
   `F_j : P_4 → P_3`, and deleting strand `i` or `j` of `A_ij` gives `1`.
   - `F_4` kills all three generators `A_14, A_24, A_34`.
   - `F_3` kills `A_34`, and `F_2` kills `A_24`. In both cases the inner commutator becomes trivial.
   - `F_1` kills `A_14`.
   - In each case the outer commutator has a trivial entry, so `F_j(b) = 1`.
2. **`Φ_0 ∈ Brun_4`.** `Brun_4` is normal in `B_4`, so `T b T^{-1} ∈ Brun_4`, and hence
   `Φ_0 = (T b T^{-1}) b^{-1} ∈ Brun_4`.
3. **`ρ̄_4(T) = I`, by hand.** `σ_1` and `σ_2` fix `e_4`. At `t = −1`,
   `M = ρ_3(σ_1σ_2)(−1) = [[2,−2,1],[1,0,0],[0,1,0]]`.
   - `M^3 = [[1,−2,2],[2,−3,2],[2,−2,1]]`, and `(M^3)^2 = I`.
   - So `ρ̄_4(T) = M^6 ⊕ 1 = I`.
4. **`ρ̄_4(Φ_0) = I`.** `ρ̄_4` is a homomorphism, so
   `ρ̄_4(Φ_0) = ρ̄_4(T) ρ̄_4(b) ρ̄_4(T)^{-1} ρ̄_4(b)^{-1} = I`.
5. **`ρ_4(Φ_0) ≠ I`, hence `Φ_0 ≠ 1`.** This is exact multiplication of the 96 generator matrices
   (script check 5). The exponents occurring in the entries span `[−14, 14]`. `ρ_4` is a
   homomorphism of `B_4`; check 1 confirms the braid relations for the implementation.

**Independent check that `Φ_0 ≠ 1`** (not used above, so it adds nothing to `requires`).
- `b` is a basic commutator in three distinct free generators of `ker F_4 ≅ F_3` (Artin
  combing), so `b ≠ 1`.
- `b` is pseudo-Anosov by `brunnian-four-braids-are-pseudo-anosov`. So `b(c) ≠ c`, where `c`
  is the round curve around `p_1, p_2, p_3`.
- `[T_c^2, b] = 1` would give `T_{b(c)}^2 = T_c^2`, hence `b(c) = c`, a contradiction.

The script also checks independently that `Φ_0` is Brunnian on the Artin action (forgetting each
strand gives the identity automorphism). ∎
