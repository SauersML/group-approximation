---
rg: 2
id: leavitt-path-k-theory-det-proof
kind: route
title: Split the ABC sequence into cokernels and kernels of 1 - N^t on Quillen's K-groups of F_q
target: leavitt-path-k-theory-over-finite-fields-via-det
requires:
  - abc-leavitt-path-k-theory-exact-sequence
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

Put `T = 1 - N^t` and `D = det T`. With no sinks and no sources, `T` is square,
and the transpose convention does not change `D` or the Smith invariants.

**Inputs.**
- **Quillen** (Ann. of Math. 96, 1972; classical, stated here, not re-read):
  `K_0(F_q) = Z`, `K_(2i-1)(F_q) = Z/(q^i - 1)`, `K_(2i)(F_q) = 0` for `i >= 1`.
- **ABC.** `abc-leavitt-path-k-theory-exact-sequence`, with `k = F_q`, gives short
  exact sequences
  `0 -> coker(T | K_n(F_q)^V) -> K_n(L) -> ker(T | K_(n-1)(F_q)^V) -> 0`.

**Linear algebra.**
- On `Z^V`, `T` is injective iff `D != 0`, and then `|coker| = |D|`.
- On `(Z/m)^V`, `T` is bijective iff `D` is a unit mod `m` (adjugate). On a
  finite module injective and surjective are equivalent.

**Degree by degree.**
- `n = 1`: coker on `(Z/(q-1))^V`, ker on `Z^V`. Both vanish iff `D != 0` and
  `gcd(D, q-1) = 1`.
- `n = 2`: `K_2(F_q) = 0`, so only ker on `(Z/(q-1))^V` remains. It vanishes iff
  `gcd(D, q-1) = 1`.
- `n = 2i-1 >= 3`: coker on `Z/(q^i - 1)`, and `K_(2i-2)(F_q) = 0`.
- `n = 2i >= 4`: `K_(2i)(F_q) = 0`, and ker on `Z/(q^i - 1)`.
- Both reduce to `gcd(D, q^i - 1) = 1`.

**Arithmetic.**
- A prime `ℓ != p` divides `q^i - 1` for `i = ord_ℓ(q)`, and `p` divides no
  `q^i - 1`. So `gcd(D, q^i - 1) = 1` for all `i` iff every prime factor of `D`
  is `p`, i.e. `D = ±p^k` (with `D != 0` from degree 1).
- Item 4 is `|coker(T | Z^V)| = |D|`.

**Example.** For `N = [[2,3],[1,2]]`, `T = [[-1,-1],[-3,-1]]` and `D = 1 - 3 = -2`.
The columns are `(-1,-3)` and `(-1,-1)`, so `(1,1)` lies in the image and
`[1] = 0` in `K_0 = Z/2`. `∎`
