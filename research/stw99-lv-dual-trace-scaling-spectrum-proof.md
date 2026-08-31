---
rg: 2
id: stw99-lv-dual-trace-scaling-spectrum-proof
kind: route
title: Use the canonical dual-equivariant crossed-product isomorphism
target: stw99-lv-dual-trace-scaling-spectrum-cocycle-invariant
requires: []
artifacts:
  - research/artifacts/stw99-late-band-audit-2026-08-31.md
---

Suppose first that `beta_t=Ad(u_t) after alpha_t`, where `u` is a strictly
continuous `alpha`-cocycle.  On canonical generators, exterior equivalence
gives an isomorphism

```text
Phi:A rtimes_beta R -> A rtimes_alpha R,
Phi(pi_beta(a))=pi_alpha(a),
Phi(lambda_beta(t))=pi_alpha(u_t) lambda_alpha(t).
```

Both dual actions fix the coefficient copy and multiply the implementing
unitary at `t` by the same scalar `exp(-ist)`.  Hence

```text
Phi after hat(beta)_s = hat(alpha)_s after Phi
```

for every `s`.  Conjugating the coefficient algebra before applying this
construction proves the same statement for cocycle conjugate flows.

Let `tau_alpha` and `tau_beta` span the respective unique tracial rays.  There
is a scalar `r>0` with `tau_alpha after Phi=r tau_beta`.  Therefore

```text
r c_beta(s) tau_beta
 = tau_alpha after Phi after hat(beta)_s
 = tau_alpha after hat(alpha)_s after Phi
 = r c_alpha(s) tau_beta,
```

so `c_alpha=c_beta`.  Rescaling either spanning trace cancels from the
definition.  Since the dual actions form an action, `c_alpha` is a positive
character of `R`.  It is automatically continuous: choose a positive element
`x` with `0<tau_alpha(x)<infinity`; norm continuity of the orbit and lower
semicontinuity of the trace make
`s |-> tau_alpha(hat(alpha)_s(x))/tau_alpha(x)=c_alpha(s)` lower
semicontinuous, and a lower-semicontinuous positive character of `R` is
continuous.  It therefore has the form `exp(-beta s)` for a unique real
`beta`.
