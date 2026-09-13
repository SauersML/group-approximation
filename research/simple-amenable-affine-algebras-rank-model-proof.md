---
rg: 2
id: simple-amenable-affine-algebras-rank-model-proof
kind: route
target: simple-amenable-affine-algebras-have-unital-rank-models
requires:
  - elek-amenable-algebras-almost-have-fd-representations
artifacts:
  - research/artifacts/un-open-4-amenable-rank-models-2026-09-13.md
title: Proof — one Følner sequence gives one Sylvester rank function, and simplicity makes it faithful
---

Full proof in §2 of the artifact. Outline.

1. **One sequence for all of `R`.** `R` is affine, hence of countable dimension. Exhaust it by finite
   dimensional `1 ∈ B_1 ⊆ B_2 ⊆ …` and apply amenability to `(B_n, 1/n)`, giving nonzero finite dimensional
   `Q_n` with `dim(B_n Q_n) ≤ (1+1/n) dim Q_n`. For each fixed `r` this gives
   `dim(r Q_n + Q_n) ≤ (1+1/n) d_n` for all large `n`, where `d_n = dim Q_n`.
2. **Compressions.** With `P_n : R → Q_n` a projection along a complement, set `φ_n(r)v = P_n(rv)`; each
   `φ_n : R → M_(d_n)(k)` is linear and unital. This is Elek's construction.
3. **Asymptotic multiplicativity.** `φ_n(rs) − φ_n(r)φ_n(s) = P_n λ(r)(1−P_n)λ(s)|_(Q_n)` has rank at most
   `dim(s Q_n + Q_n) − dim Q_n ≤ d_n/n`. So `Φ(r) = [(φ_n(r))]` is a unital homomorphism into the rank
   ultraproduct.
4. **The rank function.** `rk(r) = lim_ω dim(r Q_n)/d_n` satisfies `rk(Φ(r)) = rk(r)` and `rk(1) = 1`.
5. **`N = {rk = 0}` is a two-sided ideal.** Subadditivity is `dim((r+s)Q) ≤ dim(rQ) + dim(sQ)`; the left
   case is that `s(rQ_n)` is a linear image of `rQ_n`; the right case uses step 1 to write
   `s Q_n ⊆ Q_n + U_n` with `dim U_n ≤ d_n/n`, so `dim(rsQ_n) ≤ dim(rQ_n) + d_n/n`.
6. **Faithfulness.** `1 ∉ N`, so `N ≠ R`; simplicity forces `N = 0`, so `Φ` is injective and `rk` is a
   faithful Sylvester matrix rank function. A ring with one is stably finite.

Step 5 is the single-sequence form of Elek's "the rank radical is an ideal"; step 6 is his simple-plus-
almost-fd argument, here yielding an embedding.
