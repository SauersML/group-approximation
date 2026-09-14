---
rg: 2
id: equivariant-retract-splits-subshift-el-restriction
kind: claim
title: If a closed invariant Y is an equivariant retract of the subshift X, restriction EL_n(R_X) → EL_n(R_Y) splits with kernel E_n(R_X, I_Y)
distinct_from:
  restriction-kernel-relative-elementary-off-minimal-sets: that needs the minimal subsets outside Y to form a closed set disjoint from Y; this needs an equivariant retraction and allows minimal subsets accumulating on Y
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `equivariant-retract-splits-el-restriction-proof`.

Let X ⊆ A^Z be a subshift and Y ⊆ X closed invariant. Suppose r : X → Y is continuous with r∘T = T∘r and r|_Y = id. Let n ≥ 2. Then:
- ker(EL_n(R_X) → EL_n(R_Y)) = E_n(R_X, I_Y);
- EL_n(R_X) = E_n(R_X, I_Y) ⋊ EL_n(R_Y);
- for n ≥ 3, K_2(n,R_X) → K_2(n,R_Y) is split onto.

Example: S is the closure of the periodic orbits of (0^k1)^∞, X = X_α × S and Y = X_α × {0^∞}. The minimal subsets outside Y accumulate on Y, but (w,s) ↦ (w,0^∞) is an equivariant retraction.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS; every step re-derived (see the artifact).
