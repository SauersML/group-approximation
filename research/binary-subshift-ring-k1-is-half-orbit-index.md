---
rg: 2
id: binary-subshift-ring-k1-is-half-orbit-index
kind: claim
title: Over F_2 the half-orbit Fredholm index is an isomorphism K_1(LC(X,F_2)⋊Z) → Z, and on the topological full group it is minus the Giordano–Putnam–Skau index
distinct_from:
  minimal-cantor-crossed-product-k-theory-formula: that computes the abstract groups K_n; this identifies K_1 with an explicit operator index on an orbit and reads off which diagonal units lie in the stable elementary group
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

Let `(X,T)` be an infinite minimal Cantor system and `R_X = LC(X,F_2) ⋊_T Z`. Fix `x ∈ X`, let `R_X` act on
`V = F_2^(Z)` by `π(f)δ_n = f(T^n x)δ_n` and `π(u)δ_n = δ_(n+1)`, and let `P` project onto `span{δ_n : n ≥ 0}`.
- For `M ∈ GL_k(R_X)`, the compression `Pπ(M)P` is invertible modulo finite rank.
- Its algebraic Fredholm index `ind(M)` defines a homomorphism `GL(R_X) → Z`.
- It induces an isomorphism `K_1(R_X) → Z` with `ind(u) = −1`.

Consequences:
- `M ∈ GL_n(R_X)` with `ind(M) ≠ 0` lies in no `EL_m(R_X)`. For example `diag(u,1,1) ∉ G_X = EL_3(R_X)`.
- `diag(M, I_m) ∈ EL_(n+m)(R_X)` for some `m` iff `ind(M) = 0`.
- For `γ ∈ [[T]]` with unit `a_γ = Σ_k u^k χ_(\{n_γ = k\})`, `ind(a_γ) = −I(γ)`, where `I(γ) = ∫ n_γ dμ` is the Giordano–Putnam–Skau index.
- In particular `diag(a_γ,1,1) ∉ G_X` whenever `I(γ) ≠ 0`, while `[[T]]'` has index 0.

Proof in the `-proof` route and artifact part 1 §2. Unreviewed.
