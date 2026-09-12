---
rg: 2
id: binary-tensor-square-rank-functions-live-on-diagonal-norms
kind: claim
title: A rank function through the binary diagonal tensor square kills off-diagonal cylinder norms and must be carried by diagonal-block norm elements
distinct_from:
  odd-char-leavitt-unit-tensor-images-have-no-rank-function: that rules out every rank function in odd characteristic for degrees below the characteristic; this is the characteristic-two tensor square, where no contradiction is reached and the survivors are localized instead.
  binary-leavitt-unit-tensor-images-have-no-rank-function: that is the open no-go for the binary square; this establishes where any counterexample to it must put its rank.
artifacts:
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-tensor-rankfn`; verification requested from `w3-vf-linear`) by
`binary-tensor-square-diagonal-norm-localization-proof`.

**Setup.** `R = L_(F_2)(1,2)`, `Γ = R^x`, and `B_2 = span{g ⊗ g : g in Γ} ⊆ R ⊗ R`. Let `rk` be a Sylvester
matrix rank function on any ring receiving a unital ring map from `B_2`.

**Statements.**
1. **Tate–Frobenius quotient:** `x -> [x ⊗ x]` gives `B_2/(B_2 ∩ N) ≅ R`, where `N` is the image of
   `1 + flip`. So `rk` is positive on some symmetrized element of `B_2`.
2. **Null off-diagonal norms:** for disjoint nonempty clopens `X`, `Y` with proper union,
   `Sym(p_X, p_Y) = p_X ⊗ p_Y + p_Y ⊗ p_X` lies in `B_2` and has rank `0`.
   - *Proof idea:* four commuting square-zero norms `Sym(u_(X_a X'), u_(Y_b Y'))` act as isometries with
     orthogonal ranges inside one Thompson-conjugate corner.
3. **Localization:** for every clopen partition into at least 3 pieces,
   - `Q_P = Σ_i p_(A_i) ⊗ p_(A_i)` has rank `1`;
   - `rk z = rk(Q_P z Q_P)` for every `z in B_2`.

**Consequence.** Any detecting rank function built through `W ⊗ W` over `F_2` has to live on diagonal-block
norm elements `Sym(p_i a p_j, p_i b p_j)` at every scale. The two-root defect is only reached through them.
