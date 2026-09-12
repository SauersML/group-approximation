---
rg: 2
id: iwahori-second-order-repair-empty-proof
kind: route
title: Read the mismatch kernel off uniform rigidity at zero defect, then apply the integrability screen
target: iwahori-second-order-repair-space-is-empty
requires:
  - iwahori-uniform-infinitesimal-rigidity
  - integrable-neutral-directions-pay-no-second-order
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

## Proof

**Chart and tangent space.** Each modular vertex is `C_4 *_(C_2) C_6`.
In a unitary representation its common central involution splits the space
into its two eigenspaces. On either eigenspace the generators of orders
four and six have fixed allowed eigenvalues and locally fixed
multiplicities; their eigenspaces vary in independent unitary flag
manifolds. Allowing the central eigenspace decomposition to vary gives
local smooth charts for the representation variety. Differentiating the
representation relations gives exactly the anti-Hermitian cocycles.
This argument supplies smooth charts in each fixed dimension, with no
dimension-uniform derivative estimate asserted.

The residual is smooth. At a compatible base point its derivative in the
`b`-coordinate is `(c_1(b)-c_2(sigma b))rho(b)`. Right multiplication by
the fixed unitary `rho(b)^*` is an isometry of the residual space and
identifies this derivative with the Mayer-Vietoris mismatch map of the
first prerequisite. This fixed change of residual coordinates also
preserves the assertion that the quadratic term belongs to its range.

**Kernel.**  Apply `(UIR)` to a pair with `def(c_1, c_2) = 0`: there is a common
`x in M_d` with `max_i ||c_i - delta x||_2 <= sigma_0^(-1) * 0 = 0`, so
`c_1 = c_2 = delta x`.  Conversely every diagonal coboundary is in the kernel.
The pair being anti-Hermitian, `x` may be taken anti-Hermitian.  (The first
prerequisite is available because `pi` is compatible, hence the restriction of a
representation of `SL_2(Z[1/2])`, hence finite-image and congruence by the
superrigidity/CSP inputs explicitly recorded in that prerequisite.)

**Integrability.**  For anti-Hermitian `x` the curve
`u(t) = exp(t x) in U(d)` gives the pair
`pi(t) = (u(t) pi_+ u(t)^*, u(t) pi_- u(t)^*)`, which consists of unitary
representations of `V_1, V_2` and satisfies

```text
pi_+(t)|_B = u(t) pi_+|_B u(t)^* = u(t) (pi_- o sigma) u(t)^* = pi_-(t) o sigma,
```

so `F(pi(t)) = 0` for all `t`, and `pi'(0) = (delta x, delta x)`.

**Conclusion.**  Every element of `ker DF(pi)` is therefore integrable at `pi`,
and the second prerequisite gives `Pi D^2F(pi)[xi, xi] = 0` for each of them,
which is `(E1)`.

**Padding.**  If `rho'` is any representation of `SL_2(Z[1/2])` then
`rho (+) rho'` is again a representation of `SL_2(Z[1/2])`, hence congruence,
and the argument applies to it unchanged.
