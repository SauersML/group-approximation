---
rg: 2
id: root-measures-integer-matrices-serre-violation-proof
kind: route
title: Compute the golden-ratio root measure and tensor it with the arcsine law
target: root-measures-of-integer-matrices-can-violate-serre
requires: []
---

**Eigenvectors.** `B = [[0,1],[1,1]]` has characteristic polynomial
`x^2 - x - 1`, with roots `phi` and `psi = -1/phi`. Since `lambda^2 = lambda + 1`,
the vector `(1, lambda)` satisfies `B (1,lambda) = (lambda, 1+lambda) = lambda (1,lambda)`.
Normalizing, the weight of `e_1` on the `lambda`-eigenspace is `1/(1+lambda^2)`.

**Root measure at `e_1`.**

```text
rho_1 = (1/(1+phi^2)) delta_phi + (1/(1+psi^2)) delta_psi
      = (1/(1+phi^2)) delta_phi + (phi^2/(1+phi^2)) delta_psi,
```

and the weights sum to 1. Hence

```text
integral log|x| d rho_1 = (1/(1+phi^2)) log phi - (phi^2/(1+phi^2)) log phi
                        = log(phi) (1 - phi^2)/(1 + phi^2).
```

With `phi^2 = phi + 1 ~ 2.618`, this is `~ 0.4812 * (-0.4472) ~ -0.2152`.
The same computation at `e_2` gives weights `phi^2/(1+phi^2)` and
`1/(1+phi^2)` and the opposite sign. The two log integrals sum to
`log|phi psi| = log|det B| = 0`.

**Integer moments.** By induction `B^k = [[F_(k-1), F_k],[F_k, F_(k+1)]]` with
`F_0 = 0`, `F_1 = 1`. So `integral x^k d rho_1 = <B^k e_1, e_1> = F_(k-1)`.

**Necklace test.** For `Q = x`, `N_j = F_(j-1)` gives `N_1 = 0` and `N_2 = 1`,
so `p_2 = (N_2 - N_1)/2 = 1/2` is not an integer.

**Atomless version.** Let `C = g + g^-1` on `l^2(Z)`, with root measure `alpha`
at `delta_0` equal to the arcsine law on `[-2,2]`. The spectral measure of
`B (x) C` at `e_1 (x) delta_0` is the image of `rho_1 (x) alpha` under
`(s,t) -> st`, i.e. `rho_1 boxtimes alpha`.
- **No atoms:** `alpha` is absolutely continuous and `rho_1` has no atom at `0`.
- **Integer moments:** `<(B(x)C)^j e_1(x)delta_0, e_1(x)delta_0> = F_(j-1) c_j`, where
  `c_j` counts closed walks of length `j` on `Z`.
- **Log integral:** `integral log|st| d(rho_1 (x) alpha) = integral log|s| d rho_1 + integral log|t| d alpha`.
  The second term is `m(x + 1/x) = m(x^2 + 1) = 0` by Jensen, since the roots `+-i` lie on the unit circle.
  So the total is `~ -0.2152 < 0`.
- **Necklace test fails:** `N_2 = F_1 * 2 = 2` and `N_4 = F_3 * 6 = 12`, so `p_4 = (N_4 - N_2)/4 = 5/2`.

**Galois weights.** `phi` and `psi` are Galois conjugate, and `rho_1` gives
them unequal masses `1/(1+phi^2) != phi^2/(1+phi^2)`. QED.
