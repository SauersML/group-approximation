---
rg: 2
id: covariant-separable-relative-signal-ceiling-proof
kind: route
title: The separable fidelity bound pins the isotropic coefficient
target: covariant-separable-relative-signal-ceiling
requires: []
---

For a product pure state `|a><a| tensor |bar b><bar b|`,

```text
|<Omega_d, a tensor bar(b)>|^2 = d^{-1}|<b,a>|^2 <= 1/d.
```

By convexity every separable state has isotropic fidelity `F <= 1/d`. For a
trace-one isotropic state `rho = beta I + gamma |Omega><Omega|`, eliminating
`beta` gives

```text
gamma = (d^2 F-1)/(d^2-1).
```

Hence `gamma <= 1/(d+1)`.
