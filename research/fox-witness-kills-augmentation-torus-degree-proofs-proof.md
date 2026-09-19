---
rg: 2
id: fox-witness-kills-augmentation-torus-degree-proofs-proof
kind: route
title: The Fox fundamental formula makes the Jacobian kill the generator column, and perfection gives an integral left inverse of its augmentation
target: fox-witness-kills-augmentation-torus-degree-proofs
requires: []
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
  - experiments/torus-fox-witness-2026-09-17/check_fox_witness.py
---

Artifact Section 3 (Theorem B). This is self-contained algebra.

1. **Fundamental formula.** For every word `r` in the free group `F`,
   `sum_i (d r / d x_i)(x_i - 1) = r - 1` holds in `Z[F]`.
   - Induct on word length, using `d(uv)/dx_i = du/dx_i + u dv/dx_i`,
     `dx_i/dx_i = 1` and `d(x_i^{-1})/dx_i = -x_i^{-1}`.
   - In `Z[L]` each `r_j` maps to 1, so `J c = 0` for `c = (x_i - 1)_i`.
2. **Integral left inverse.**
   - `epsilon(d r_j / d x_i)` is the exponent sum of `x_i` in `r_j`.
   - `H_1(L; Z) = Z^n / span_Z{exponent-sum vectors}`, which is 0 because `L` is perfect.
   - `Z^n` is noetherian, so finitely many relators `r_1..r_k` span. The map `Z^k -> Z^n` that
     sends `e_j` to the exponent-sum vector of `r_j` is then a surjection onto a free abelian
     group, so it splits. Transposing a splitting gives `P in M_{n x k}(Z)` with
     `P epsilon(J) = I_n`.
3. **The witness.** `D_0 = P J` has `epsilon(D_0) = I_n` and `D_0 c = P (J c) = 0`. Its
   conjugate transpose `D = D_0^*` has `epsilon(D) = I_n`, since `epsilon` commutes with `*`, and
   `c^* D = (D_0 c)^* = 0`.
4. **Nonzero.** `c^* != 0` because `x_1 != 1` and `Z[H]` has `H` as a basis. Everything lies in
   `Z[L] subset Z[H]`.
5. **Higman's group.** Nontrivial generators: if one generator is 1, the relations force the
   next to be 1, so all are. But Higman's group is infinite; this is recalled, and is the
   standing hypothesis of `higman-group-algebra-not-stably-finite`. The reduced rows come from
   `x_{i-1}^{-1} x_i x_{i-1} = x_i^2`. The row-0 check is in the artifact.
6. **Machine check.** `experiments/torus-fox-witness-2026-09-17/check_fox_witness.py`:
   - Part A: the formula holds exactly in `Z[F]` for Higman, `A_5` and `BS(2,3)`, and
     `epsilon(D_0) = I` for Higman (`P` a signed permutation) and for `A_5`
     (`P = [[23,15,-9],[-5,-3,2]]`).
   - Part B: `c^* D = 0` exactly in the right regular representation of `A_5`, with rank 61 of
     120.
