---
rg: 2
id: tracial-domination-is-not-state-domination-proof
kind: route
title: Two rank-one operators separate the trace weight from a pure state weight
target: tracial-domination-is-not-state-domination
requires: []
---

**(i)**  With (TDS1), `Tr A = 1` and `Tr B = (d-1)/(d-1) = 1`, so
`tau(A) = tau(B) = 1/d` and the trace-weighted domination holds with constant
`1`.  Evaluating at `rho = |psi><psi|` gives `Tr(A rho) = <psi|A|psi> = 1`
and `Tr(B rho) = <psi|B|psi> = 0`, which is (TDS2).  If `A <= cB` held as
operators, evaluating the form at `psi` would give `1 <= 0`.

**(ii)**  For `A >= 0` and a state `rho`, write `rho <= ||rho||_inf I` and use
positivity of the trace against `A >= 0`:

```text
Tr(A rho) <= ||rho||_inf Tr(A I) = ||rho||_inf Tr(A),
```

and `Tr(A) = d tau(A)` by definition of the normalized trace.  Equality
analysis: `||rho||_inf >= 1/d` for every state with equality iff
`rho = I/d`, and `||rho||_inf = 1` iff `rho` is pure, giving the two stated
values of the factor.

Nothing here depends on the particular tracial theorems named in the claim;
they are cited only to identify which side of (TDS3) they live on.  Their own
statements make this explicit: both are quadratic-form inequalities in the
normalized Hilbert--Schmidt norm.
