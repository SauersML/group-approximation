---
rg: 2
id: serre-class-admits-non-integral-atoms-proof
kind: route
title: Equilibrium potentials of long intervals pay for the negative logarithms at a rational non-integer atom and at unequal conjugate atoms
target: serre-class-admits-non-integral-atoms
requires:
  - integer-root-limits-are-galois-balanced-serre-measures
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

Artifact `determinant-spectral-atoms-2026-09-12.md`, Section 4.

**Potential bound.** Write `zeta = (R/2)(u + 1/u)` with `|u| >= 1`. Then
`U_R(zeta) = integral log|zeta - t| d omega_R(t) = log(R|u|/2) >= log(max(R,|zeta|)/2)`.
So for nonzero `Q = c prod_j (t - z_j) in Z[t]`,

```text
I_R(Q) = integral log|Q| d omega_R = log|c| + sum_j U_R(z_j) >= deg(Q) log(R/2).     (P)
```

**`mu_1`.**
- If `Q(1/2) = 0`, the value is `I_4(Q)/2 >= 0`.
- Otherwise `2^(deg Q) Q(1/2)` is a nonzero integer, so
  `log|Q(1/2)| >= -deg(Q) log 2`, and the value is at least
  `(deg Q / 2)(log 2 - log 2) = 0`.

**`mu_2`.**
- **Sup bound.** For `|z| <= 3`, `3 + |zeta| <= 2 max(6, |zeta|)` gives
  `log|Q(z)| <= I_6(Q) + 2 deg(Q) log 2`.
- **Vanishing case.** If `Q(phi^2) = 0`, the conjugate is also a zero, and the
  value is `0.6 I_6(Q) >= 0`.
- **Otherwise.** Put `u = log|Q(phi^2)|`, `v = log|Q(phi^-2)|`, so
  `u + v = log|N(Q(phi^2))| >= 0`. Then

  ```text
  0.3u + 0.1v + 0.6 I_6 = 0.1(u+v) + 0.2u + 0.6 I_6 >= -0.2v + 0.6 I_6
                        >= 0.4 I_6 - 0.4 deg(Q) log 2 >= 0.4 deg(Q) log(3/2) >= 0.
  ```

**Not integer-matrix limits.** By `integer-root-limits-are-galois-balanced-serre-measures`
(artifact `determinant-integer-root-limits-2026-09-12.md`, Section 2.2), a limit
of eigenvalue distributions of integer matrices with real spectrum gives mass
`0` to non-integral algebraic numbers, and equal mass to conjugates. `mu_1` and
`mu_2` violate this. QED
