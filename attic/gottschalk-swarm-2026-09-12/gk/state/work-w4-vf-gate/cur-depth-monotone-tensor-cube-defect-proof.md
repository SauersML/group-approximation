---
rg: 2
id: depth-monotone-tensor-cube-defect-proof
kind: route
title: The anti-central corner of a sofic group algebra, and the tensor cube of the stably finite depth-monotone embedding
target: depth-monotone-units-carry-weakly-finite-nonzero-defect
requires:
  - depth-monotone-leavitt-subalgebras-are-stably-finite
  - linear-sofic-group-algebra-is-stably-finite
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---
Artifact Section 4 (Theorems 4.1 and 4.3, Corollary 4.2) and Lemma 3.1. Held OPEN until `w4-vf-gate` re-derives it.
1. **Sofic corner** (Theorem 4.1). `ε_-` is a central idempotent of the stably finite `F_3[Γ_0]`, so the corner is
   weakly finite. `D = 2(1 - [z])(x_23 x_12 - x_23 - x_12 + 1)` involves eight distinct group elements.
2. **Depth-monotone units** (Corollary 4.2). For `ω(0) <= ω(1)`, `H^ω_≤` contains `z`, `x_12(1)` and `x_23(1)`, and
   over `F_3` it is LEF, hence sofic.
3. **Tensor cube** (Theorem 4.3). Restrictions to the invariant `F_k` are multiplicative for large `k`, and finitely
   many `k` vanish in the quotient. In `Σ m^T n^S`, the `12` ordered pairs of nonempty disjoint subsets of `{1,2,3}`
   give distinct elementary tensors in `1`, `n`, `m`. These three are independent, as `1_[10]` and `1_[11]` show.
4. **Algebra level** (Lemma 3.1). `t_11 s_0 = 0`, so every unital algebra homomorphism kills `D`.
