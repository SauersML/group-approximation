---
rg: 2
id: affine-extension-of-fp-elementary-group-is-fp
kind: claim
title: R^n x| E_n(R) is finitely presented whenever E_n(R) is, for a finitely generated commutative ring R and n >= 4
distinct_from:
  rational-linear-groups-satisfy-boone-higman: that includes Zaremsky's hand presentation of Z[1/m]^n x| GL_n(Z[1/m]) for its one ring; this is a general lemma for elementary groups over every finitely generated commutative ring.
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`affine-extension-of-fp-elementary-group-is-fp-proof`. Not independently reviewed.

**Hypotheses.**
- `R` is a commutative ring, generated as a ring by a finite set `T`.
- `n >= 4`.
- `E_n(R)` is finitely presented.

**Conclusion.** The affine group `R^n x| E_n(R)` is finitely presented. Explicitly,
let `S = T ∪ {1}`. It has the presentation with the following generators and
relations.
- **Generators:** `x_ij(ε)` for `i != j` and `ε in S`, and `τ_1, ..., τ_n`.
- **(E)** Finitely many relators presenting `E_n(R)` on the `x_ij(ε)`.
- **(C1)** `[x_ij(ε), τ_k] = 1` for `k != j`.
- **(C2)** `x_ij(1) τ_j x_ij(1)^-1 = τ_j τ_i`.
- **(C3)** `[τ_k, τ_l] = 1`.

Here `x_ij(ε)` maps to `e_ij(ε)`, `τ_i` maps to the translation by `e_i`, and
`[a,b] = aba^-1b^-1`.

**Why `n >= 4`.** Every step of the proof chooses an index outside a set of three.
