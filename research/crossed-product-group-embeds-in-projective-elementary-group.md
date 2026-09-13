---
rg: 2
id: crossed-product-group-embeds-in-projective-elementary-group
kind: claim
title: Any group of units embeds in EL_N modulo its centre through Whitehead's lemma, so non-LEF and nonsofic units pass to the projective elementary group
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `R` be a unital ring and `θ : Γ -> R^×` an injective homomorphism.
- For `N >= 2`, `ι(g) = diag(θ(g), θ(g)^(-1), 1_(N-2))` is an injective homomorphism `Γ -> EL_N(R)`.
- For `N >= 3`, `ι(Γ)` meets `Z(EL_N(R))` trivially, so `Γ` embeds in `EL_N(R)/Z(EL_N(R))`.

**Instances.**
- For a crossed product `LC(X,k) ⋊ Γ`, `θ(g) = u_g`.
- Topological full-group units embed the same way.

**Consequences.**
- LEF, soficity, linear soficity and hyperlinearity pass to subgroups.
- So a non-LEF (or nonsofic) acting group makes every `EL_N(R)/Z`, `N >= 3`, non-LEF (or nonsofic).

Route: `crossed-product-group-projective-elementary-embedding-proof`.

**Review (un-verify-3, 2026-09-13): PASS.** `w(v)w(−1) = diag(v, v^(-1)) ∈ E_2`, and `diag(v, v^(-1), 1) e_13(1) diag(v^(-1), v, 1) = e_13(v)` detects central units. `research/artifacts/un-review3-2026-09-13-part3.md` §7.
