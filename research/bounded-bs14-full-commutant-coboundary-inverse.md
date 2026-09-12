---
rg: 2
id: bounded-bs14-full-commutant-coboundary-inverse
kind: claim
title: Bounded BS orbit length and monodromy order give a KM/4 inverse on the full base commutant
artifacts:
  - research/artifacts/bs14-full-commutant-preconditioning-2026-08-22.md
  - experiments/bs14_monodromy_quantization_check.py
distinct_from:
  bounded-cycle-coboundary-inverse: that controls only an abstract sum of coordinate cycles; this controls the entire noncommutative base commutant, including off-diagonal multiplicity and packet-monodromy directions.
  weyl-defect-koopman-spectral-regularity: that concerns the particular transported arithmetic defect; this supplies the exact finite-period inverse on every nonfixed commutant direction after packet preconditioning.
  bs14-monodromy-admits-root-of-unity-quantization: that constructs finite-order packet returns; this converts their finite order into the full commutant coboundary estimate.
---

Let `R,S in U(d)` satisfy `R S R^(-1)=S^4`.  Assume every fourth-power orbit
in `spec(S)` has length at most `K` and every scalar packet monodromy is an
`M`th root of unity, where `K,M>=2`.  Put

```text
Z={S}',                    psi=Ad(R)|_Z,
```

and let `E:Z->ker(1-psi)` be the Hilbert--Schmidt orthogonal projection.  For
every `x in Z` there is a unique minimum-norm `y` orthogonal to the fixed
algebra such that

```text
(1-psi)y=x-Ex,                                         (BFC1)
```

and

```text
||y||_2 <= [2 sin(pi/(KM))]^(-1)||x-Ex||_2
       <= (KM/4)||x-Ex||_2.                            (BFC2)
```

The estimate is dimension-free once `K,M` are fixed and applies to every
matrix direction in `{S}'`, not merely to functions of `S`.
