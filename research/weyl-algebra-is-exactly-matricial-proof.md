---
rg: 2
id: weyl-algebra-is-exactly-matricial-proof
kind: route
title: Truncated polynomial multiplication and differentiation satisfy the Weyl relation exactly in M_p(F_p)
target: weyl-algebra-is-exactly-matricial
requires: []
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

1. **The exact relation.** On `V_p = F_p[t]/(t^p)` with basis `1, t, …, t^(p−1)`, let `T_p` be multiplication by
   `t` and `D_p = d/dt`. For `j < p−1`: `[D_p, T_p] t^j = (j+1)t^j − j t^j = t^j`. For `j = p−1`:
   `T_p t^(p−1) = t^p = 0`, so `[D_p, T_p] t^(p−1) = −(p−1) t^(p−1) = t^(p−1)` in characteristic `p`. Hence
   `D_p T_p − T_p D_p = 1` in `M_p(F_p)`.
2. **The map.** `a/b ↦ (a b^-1 mod p)_p` defines a unital ring homomorphism `Q → ∏_ω F_p`, for `p` not dividing
   `b`, which is ω-almost all `p`. Each element of `A_1(Q)` has a unique PBW normal form `Σ c_ij x^i y^j`. Send it
   to `(Σ (c_ij mod p) T_p^i D_p^j)_p`.
   - For each finite set of denominators this is coordinatewise induced by the ring homomorphisms
     `Z[1/b]<x,y>/(yx − xy − 1) → M_p(F_p)` for `p ∤ b`, which exist by step 1.
   - So it is a unital ring homomorphism `A_1(Q) → ∏_ω M_p(F_p)`.
3. **Injectivity.** `A_1(Q)` is simple in characteristic 0, so the kernel, a proper two-sided ideal (`1 ↦ 1`), is
   zero.
4. **No finite-dimensional modules.** If `V ≠ 0` is a finite-dimensional `Q`-vector space module, then
   `tr(yx − xy) = 0 ≠ dim V = tr(1)`.
