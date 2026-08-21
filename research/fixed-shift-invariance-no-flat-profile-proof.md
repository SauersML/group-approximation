---
rg: 2
id: fixed-shift-invariance-no-flat-profile-proof
kind: route
title: Triangular Folner profiles disprove fixed-shift-to-flat inference
target: fixed-shift-invariance-does-not-force-flat-profile
requires: []
artifacts:
  - research/artifacts/sl3-projective-rcc-audit-2026-08-21.md
---

Let `c_N=2/((N+1)(N+2))` and `mu_N(k)=c_N(k+1)` on the cyclic group
`Z/(N+1)Z`. This is a probability measure because

```text
sum_(k=0)^N (k+1) = (N+1)(N+2)/2.
```

For the unit cyclic shift, every non-wrap difference has absolute value
`c_N`, while the wrap difference has absolute value `N c_N`. Hence

```text
||mu_N-shift_1(mu_N)||_1 = 2 N c_N
                              = 4N/((N+1)(N+2)),
TV(mu_N,shift_1(mu_N)) <= 2/(N+1).
```

The triangle inequality gives, for each fixed `r`,

```text
TV(mu_N,shift_r(mu_N)) <= 2|r|/(N+1) -> 0.
```

Also `max mu_N=2/(N+2)->0`. On the other hand, comparison with the
uniform measure is a Riemann sum:

```text
TV(mu_N,u_N)
 = (1/2) sum_(k=0)^N |2(k+1)/((N+1)(N+2))-1/(N+1)|
 -> (1/2) integral_0^1 |2x-1| dx = 1/4.
```

Now put `nu_N=mu_N tensor mu_N` on `(Z/(N+1)Z)^2`. The preceding
one-dimensional estimate and tensorization show asymptotic invariance under
every fixed vector translation. Its largest atom tends to zero. Yet
marginalization contracts total variation and sends `nu_N` to `mu_N` and
Haar to `u_N`, so

```text
TV(nu_N,Haar_N) >= TV(mu_N,u_N) -> 1/4.
```

This proves the claim and directly invalidates the flatness step in
`lambda-exact-p-three-closure-route`.
