---
rg: 2
id: leavitt-completeness-transport-formula-for-root-data
kind: claim
title: The Leavitt completeness relation reaches EL_3 root data as a circle sum plus reversed-order defects
distinct_from:
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the commutator identities for the isometry pairs t_i, s_j, where t_i s_j = delta_ij; this records the completeness pairs s_i, t_i, where s_0 t_0 + s_1 t_1 = 1, and computes the exact completeness defect at root level.
  toeplitz-isometry-defects-have-total-rank-at-least-one: that shows completeness is not needed for the rank contradiction; this is what completeness looks like in root data, for test rings without a rank function.
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

**ESTABLISHED** by `leavitt-completeness-transport-formula-proof`. Elementary; no priority is claimed.

**Setting.**
- `K` is a field of characteristic two, `R = L_K(1,2)` and `e_i = s_i t_i`.
- `M` is any unital `K`-algebra. No rank function is needed.
- `sigma : EL_n(R) -> M^x` is a homomorphism with `n >= 3`, and `n_ab(r) = sigma(x_ab(r)) - 1`.
- For distinct indices `a, b, c` put `A_i = n_ab(s_i)`, `B_i = n_bc(t_i)`, `E_i = n_ac(e_i)` and
  `N = n_ac(1)`.

Then:

```text
(a)  N = E_0 + E_1 + E_0 E_1,   E_0 E_1 = E_1 E_0,   N^2 = E_i^2 = 0 ;
(b)  E_i = A_i B_i + B_i A_i + A_i B_i A_i + B_i A_i B_i + A_i B_i A_i B_i ;
(c)  A_0 B_0 + A_1 B_1 = N + E_0 E_1 + rho_0 + rho_1,
     rho_i = B_i A_i + A_i B_i A_i + B_i A_i B_i + A_i B_i A_i B_i .
```

**Reading.**
- **Natural models.** Take `n_ab(r) = rho(r) E_ab` for a unital ring homomorphism `rho : R -> P`, in
  `M = M_n(P)`. There `E_0 E_1 = 0` and every `rho_i = 0`, so (c) is the honest completeness
  `sum rho(s_i) rho(t_i) = 1` at matrix position `(a, c)`. These models have `D = N_23 N_12 = 0`.
- **General models.** The root-level completeness defect is exactly `E_0 E_1 + rho_0 + rho_1`:
  - `E_0 E_1 = N - E_0 - E_1` measures the failure of the root map to be additive on the two halves
    of `1`;
  - `rho_0 + rho_1` are the reversed-order terms.
  Among the Steinberg relations the ring enters only through additivity of each root map and the
  commutator formula, so this is the form completeness takes there. Relations of `EL_n(R)` beyond
  Steinberg are not analyzed.
- **Corner units need a return operator.** `N` is square-zero, so no root-level completeness sum is
  a nonzero idempotent. In a regular ring, take `W` with `N W N = N`. Then `e = N W` is idempotent,
  and the placement `S_i = A_i`, `T_i = B_i W` has completeness defect exactly
  `(E_0 E_1 + rho_0 + rho_1) W`.
