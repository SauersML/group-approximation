---
rg: 2
id: combine-bs14-cycle-and-monodromy-preconditioning
kind: route
title: Truncate fourth-power cycles, quantize packet returns, and invert the resulting adjoint action
target: bs14-full-commutant-finite-period-preconditioner
requires:
  - bs14-long-cycles-admit-bounded-period-shadowing
  - bs14-monodromy-admits-root-of-unity-quantization
  - bounded-bs14-full-commutant-coboundary-inverse
---

Apply `bs14-long-cycles-admit-bounded-period-shadowing` with cap `K` to obtain
an exact same-dimensional pair `(R_K,S_K)`.  Its bounds give

```text
||R-R_K||_2 <= sqrt(8/K),
||S-S_K||_2^2 <= 2pi^2/(9K).
```

Apply `bs14-monodromy-admits-root-of-unity-quantization` to `(R_K,S_K)` with
order `M`.  This leaves `S_K` and its orbit cap unchanged, preserves the BS
relation exactly, and gives an exact `R_(K,M)` with

```text
||R_K-R_(K,M)||_2 <= pi/M.
```

The triangle inequality proves `(BFP3)`.  The hypotheses of
`bounded-bs14-full-commutant-coboundary-inverse` now hold, so `(BFP4)` follows.
