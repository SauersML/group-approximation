---
rg: 2
id: state-pinned-regular-element-ranks-proof
kind: route
title: Retracts through a matrix bound the state from below and factorizations bound it from above; regular elements make the bounds meet
target: rank-functions-extending-a-state-are-pinned-on-regular-elements
requires: []
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Section 2.
1. If `f = L X R` and `X = U e V`, then `f = (LU) e (VR)`, so `fA^k` is a retract of `eA^(k')` and
   `s(f) <= s(e)`.
2. `N(U e V) <= N(e) = s(e)` and `s(f) = N(L X R) <= N(X)`.
3. For `X = XYX`, `e = XY` is idempotent, `X = eX` factors through `eA^m`, and `e = I·X·Y`.
4. **The ring `F_3[C_3]`.** It is local, so `K_0 = Z` and the state is unique.
   - **Bounds from s.** Idempotents `L(x-1)R` lie in matrices over the radical, hence are 0, so
     `rho^s(x-1) = 0`. Every projective is free and `x - 1 != 0`, so `rho_s(x-1) = 1`.
   - **Realized values.** The normalized rank on `F_3[x]/(x-1)^j` gives `(j-1)/j` for `j = 1, 2, 3`, and
     convex combinations fill `[0, 2/3]`.
   - **Upper bound.** Frobenius `N(AB) + N(BC) <= N(B) + N(ABC)` follows from triangular
     superadditivity. With `u = x-1` and `u^3 = 0` it gives `2N(u) <= 1 + N(u^2)` and
     `2N(u^2) <= N(u)`, so `N(u) <= 2/3`.

No imports.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 29.3 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the retract through `f a e` and `e b f`, and regular elements via `e = XY`;*
- *`F_3[C_3]` is local, and `N_j` gives `0`, `1/2`, `2/3`;*
- *the Sylvester and Frobenius inequalities with `u^3 = 0`.*
