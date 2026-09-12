---
rg: 2
id: odd-char-leavitt-unit-tensor-images-have-no-rank-function
kind: claim
title: Below the characteristic, diagonal tensor powers of the Leavitt unit group algebra admit no Sylvester rank function
distinct_from:
  leavitt-rank-functions-killing-two-root-defect-are-augmentation: that shows the rank of the two-root defect decides every rank function on the group algebra; this rules out every rank function that factors through a diagonal tensor power of degree below the characteristic, one of the construction handles for giving the defect positive rank.
  binary-leavitt-units-carry-nonaugmentation-rank-function: that is the binary construction target; this is an odd-characteristic no-go for one construction handle, which fails in characteristic two exactly because 2 = 0.
artifacts:
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-tensor-rankfn`; verification requested from `w3-vf-linear`) by
`odd-char-leavitt-unit-tensor-images-no-rank-function-proof`.

**Setup.**
- `K` is a field of characteristic `p > 0`, `R = L_K(1,2)` and `Γ = R^x`.
- For `n >= 1`, `Δ_n : K[Γ] -> R^(⊗n)` sends `[g]` to `g^(⊗n)`, and `B_n` is its image.

**Statement.** If `2 <= n < p`:
- no ring that receives a unital ring homomorphism from `B_n` carries a Sylvester matrix rank function;
- equivalently, every Sylvester matrix rank function on `K[Γ]` is nonzero somewhere on `ker Δ_n`.

**Consequences.**
- **Tensor-power constructions:** take any `R`-module `W` with `Γ` acting diagonally on `W^(⊗n)`, `n < p`.
  No normalization of ranks of these operators gives a Sylvester rank function. That covers densities,
  depth filtrations, ultraproducts and regular envelopes.
- **Ternary case:** for `K = F_3`, diagonal tensor squares cannot produce the detecting rank function on
  `F_3[L_(F_3)(1,2)^x]` that would refute the ternary corner.
- **Scope:** characteristic two is untouched. It is the open
  `binary-leavitt-unit-tensor-images-have-no-rank-function`.
