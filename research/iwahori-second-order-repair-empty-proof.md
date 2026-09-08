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

**Chart and tangent space.**  `V_i` is an amalgam of finite groups, hence acts
on a tree with finite stabilizers, hence has cohomological dimension one over
`Q`; deformations of a unitary representation of `V_i` are therefore
unobstructed and `Z^1(V_i, Ad rho)` is the tangent space at `rho|_(V_i)`.  The
residual `F` is a fixed polynomial in the generator matrices, so it is smooth,
and its differential in these coordinates is the Mayer-Vietoris mismatch map
`(c_1, c_2) -> (c_1 - sigma^* c_2)|_(S_B)` whose norm is the linearized defect
`def(c_1, c_2)` of the first prerequisite.

**Kernel.**  Apply `(UIR)` to a pair with `def(c_1, c_2) = 0`: there is a common
`x in M_d` with `max_i ||c_i - delta x||_2 <= sigma_0^(-1) * 0 = 0`, so
`c_1 = c_2 = delta x`.  Conversely every diagonal coboundary is in the kernel.
The pair being anti-Hermitian, `x` may be taken anti-Hermitian.  (The first
prerequisite is available because `pi` is compatible, hence the restriction of a
representation of `SL_2(Z[1/2])`, hence congruence by the congruence subgroup
property.)

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
