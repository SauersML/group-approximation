---
rg: 2
id: integrable-neutral-directions-second-order-proof
kind: route
title: Differentiate the exact curve twice and read the second derivative in the range
target: integrable-neutral-directions-pay-no-second-order
requires: []
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

## Proof

The function `t -> F(x(t))` is identically zero and `C^2`, so both its
derivatives vanish at `t = 0`.  The first gives `L xi = 0`, so `xi` is indeed a
neutral direction.  The second is

```text
0 = (d^2/dt^2)|_0 F(x(t)) = D^2F(x)[xi, xi] + L x''(0),
```

so `D^2F(x)[xi, xi] = - L x''(0) in ran L`, and applying `Pi`, which kills
`ran L`, gives `(IN1)`.

For the screen: if `ker L` consists of integrable directions then
`Pi D^2F(x)[xi, xi] = 0` for every `xi in ker L`, so
`Pi(F(x) + (1/2) D^2F(x)[xi, xi]) = Pi F(x)`, which no choice of `xi` changes.
