---
rg: 2
id: ledrappier-crossed-product-is-finitely-presented-proof
kind: route
title: Permutive propagation of commutation through the row above
target: ledrappier-crossed-product-is-finitely-presented
requires: [sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

This is Proposition 5 of the artifact, Section 6. Fix a family `E` satisfying (Q1)–(Q3) with
`D = r = 1`.

1. **Observables.** Put `X(z) = sum_a zeta^a E_a(z)`. Since `p` is invertible in `k`, each `E_a(z)`
   is a polynomial in `X(z)`.
   - The three points `z`, `z + e_1` and `z + e_2` lie in one ball `z + B_1`. Their operators
     commute by (Q2).
   - By (Q3), every joint eigenpattern satisfies the rule.
   - So `X(z + e_2) = X(z) X(z + e_1)`.
2. **Rows.** Induction on `j`: `[X(w), X(w + j e_1)] = 1` for all `w`. The cases `j <= 1` are (Q2).
   For `j >= 2` put `a = X(z)`, `b = X(z + e_1)`, `c = X(z + (j-1)e_1)`, `d = X(z + j e_1)`.
   - By induction `a` commutes with `b` and `c`, `b` with `c` and `d`, and `c` with `d`.
   - Step 1 and the induction hypothesis at `z + e_2` give `[ab, cd] = 1`.
   - Hence `abcd = acdb = cdab`, so `acd = cda`, so `cad = cda`, so `ad = da`.
3. **All pairs.** Iterating step 1 writes `X(z + (j, m))`, `m >= 0`, as a product of operators in
   row `z_2` at positions `z_1 + j, ..., z_1 + j + m`. These commute with `X(z)` by step 2. For
   `m < 0`, exchange the two points.
4. **Conclusion.** So `X_L` is `1`-quantum rigid. With `r = 1`,
   `sft-crossed-product-fp-iff-quantum-rigid` makes the algebra finitely presented.
