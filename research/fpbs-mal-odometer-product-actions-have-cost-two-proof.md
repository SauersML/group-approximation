---
rg: 2
id: fpbs-mal-odometer-product-actions-have-cost-two-proof
kind: route
title: Seed the new generator on three odometer residues, close by the 2-of-3 fold rule, and telescope
target: fpbs-mal-odometer-product-actions-have-cost-two
requires:
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
artifacts:
  - research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md
---

The complete proof is Lemma 1.1, Lemma 2.1 and Theorem 2.2 of the artifact.
Its only import is the lower bound in step 5.

1. **Character.** `χ(b_n) = 1 − χ(b_{n+1})` is exactly compatibility with
   `b_n = b_{n+1} a b_{n+1}^{-2}`. The values `−1, 2, −1, 2, ...` satisfy it,
   so `χ` is defined on the directed union. The product `β × Ẑ_χ` is free
   (because `β` is) and preserves `μ × Haar`.
2. **Fold rule (Lemma 1.1).** Fix a stage, with `L = H_{n+1}`, `b = b_{n+1}`,
   `K = H_n ∋ a, k = b a b^{-2}`. Let `R' = E_K ∨ b|_A` and
   `D = { w : w R' b w }`. Then `D ⊇ A` and `D` is closed under the 2-of-3
   rule on `{w, a w, b w}`. This uses only `w ~ aw` and `b^2 w ~ baw`, and
   the latter is `k(b^2 w) = baw`. If `D` is conull then `R' = E_L`.
3. **Odometer seeds (Lemma 2.1).** In the `Z/N` coordinate the triple of `w`
   is `{q, q+1, q+t}`, with `t = χ(b_{n+1}) ∈ {−1, 2}`. Starting from
   `A_N = {0, 1, 2}` (mod `N`), coordinate `j+1` is added from `j` and `j−1`
   (`t = −1`, via `w, bw ⇒ aw`), or from `j−1` and `j` (`t = 2`, via
   `w, aw ⇒ bw`). So `D = X × Ẑ`, and `relC(E_{H_{n+1}}; E_{H_n}) ≤ 3/N` for
   every `N`.
4. **Telescoping.** Take `a`, `b_1` and `b_{n+1}|_{A_{N_n}}` with
   `Σ 3/N_n < ε`. By induction this graphing generates every `E_{H_n}`, hence
   their union, which is the whole orbit relation. So `C ≤ 2 + ε`.
5. **Lower bound.** Apply `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`
   with `c*(Gamma_mal) = 2`: a finite cost equals `2`. The same result gives
   pseudocost `2` for every free action, and fixed price iff every free action
   has finite cost.

Checks: `odometer_threshold.py` part (A) closes `{0..m}` on `Z/N` for
`t ∈ {−3, −1, 0, 1, 2, 5}`. `certify.py` checks Theorem 1.2 (the exact
converse, not needed here) on the Cayley tree of `F_2`.
