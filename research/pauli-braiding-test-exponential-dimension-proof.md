---
rg: 2
id: pauli-braiding-test-exponential-dimension-proof
kind: route
title: Convert constant robustness to a Schmidt-rank lower bound
target: pauli-braiding-test-exponential-dimension
requires:
  - pauli-braiding-test-constant-robustness
---

Let `R=2^N`.  The cited rigidity theorem gives local isometries under which a
strategy of success `1-eta` has state within `delta=p(eta)` in vector norm of

```text
Phi_R tensor aux,                                               (PBD3)
```

where `Phi_R` is maximally entangled of Schmidt rank `R`.

Every Schmidt coefficient squared of `(PBD3)` is at most `1/R`: if the
auxiliary state's squared Schmidt coefficients are `lambda_j`, those of
`Phi_R tensor aux` are `lambda_j/R`, each repeated `R` times.  A unit vector
of Schmidt rank at most `d` therefore has squared overlap at most `d/R` with
`(PBD3)` (truncate the Schmidt decomposition, or apply Eckart--Young).
Local isometries preserve the physical state's Schmidt rank, which is at most
either local dimension `d`.

If two unit vectors are within `delta`, their real overlap is at least
`1-delta^2/2`; hence their squared overlap is at least
`(1-delta^2/2)^2`.  Thus

```text
d/R >= (1-delta^2/2)^2.                                        (PBD4)
```

Choose one universal `eta_0` for which `p(eta_0)<1`, and put

```text
c_0=(1-p(eta_0)^2/2)^2>0.
```

Then `(PBD4)` gives `(PBD1)`, and `(PBD2)` gives the same-dimension
contradiction.
