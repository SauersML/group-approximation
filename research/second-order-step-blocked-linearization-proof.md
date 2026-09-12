---
rg: 2
id: second-order-step-blocked-linearization-proof
kind: route
title: Expand to third order and cancel the range component with the linear correction
target: second-order-step-beats-a-blocked-linearization
requires: []
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

## Proof

Write `v = xi + eta` and `S = F(x) + (1/2) D^2F(x)[xi, xi]`.  From `(SO1)`,
`||S|| <= e + (1/2) M_2 C^2 e = O(e)`, so by `(SO2)`
`||eta|| <= rho q ||S|| = O(e)`, and `||v|| <= C sqrt e + O(e) = O(sqrt e)`;
shrink the threshold so that `||v|| <= r_0`.

Taylor's theorem to third order gives

```text
F(x + v) = F(x) + L v + (1/2) D^2F(x)[v, v] + Rem,
||Rem|| <= (M_3 / 6) ||v||^3 = O(e^(3/2)).
```

Since `L xi = 0` and `L R` is the identity on `ran L`, while `(I - Pi)` maps
into `ran L`,

```text
L v = L eta = - (I - Pi) S.
```

Expanding the quadratic term,

```text
(1/2) D^2F(x)[v, v] = (1/2) D^2F(x)[xi, xi] + D^2F(x)[xi, eta]
                      + (1/2) D^2F(x)[eta, eta],
```

so

```text
F(x + v) = S - (I - Pi) S + D^2F(x)[xi, eta] + (1/2) D^2F(x)[eta, eta] + Rem
         = Pi S + D^2F(x)[xi, eta] + (1/2) D^2F(x)[eta, eta] + Rem.
```

Now `||Pi S|| <= C e^(3/2)` by hypothesis,
`||D^2F(x)[xi, eta]|| <= M_2 ||xi|| ||eta|| = O(e^(3/2))`,
`||D^2F(x)[eta, eta]|| = O(e^2)`, and `||Rem|| = O(e^(3/2))`.  Summing gives
`(SO3)`.  All constants are explicit in `C, rho, q, M_2, M_3`.

## Scope of the derivative bounds

Inspecting the display above, `D^2F(x)` is applied only to `(xi, xi)`,
`(xi, eta)` and `(eta, eta)`, and `D^3F` only to `(v, v, v)` along the segment
from `x` to `x + v`.  Bounds `M_2, M_3` valid on any cone containing `xi`,
`eta` and `v` therefore suffice; no bound on the full differentials is needed.
This is what makes the lemma usable in normalized Schatten norms.
