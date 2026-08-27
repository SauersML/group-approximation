---
rg: 2
id: bs14-full-commutant-finite-period-preconditioner
kind: claim
title: Every exact BS(1,4) skeleton has a same-dimensional finite-period full-commutant preconditioner
artifacts:
  - research/artifacts/bs14-full-commutant-preconditioning-2026-08-22.md
distinct_from:
  bs14-long-cycles-admit-bounded-period-shadowing: that regularizes only fourth-power orbit lengths; this also quantizes scalar monodromy and records the resulting inverse on the full base commutant.
  bs14-monodromy-admits-root-of-unity-quantization: that regularizes only the continuous return phases; this combines both packet coordinates with the noncommutative coboundary estimate.
  bounded-bs14-full-commutant-coboundary-inverse: that assumes bounded packet data; this constructs such data near every exact finite-dimensional BS skeleton.
---

Let `R,S in U(d)` satisfy `R S R^(-1)=S^4`.  For every `K,M>=2` there are
`R_(K,M),S_K in U(d)` satisfying the same relation exactly, with all
fourth-power spectral orbit lengths at most `K` and all scalar packet
monodromies `M`th roots of unity, such that

```text
||S-S_K||_2^2 <= 2 pi^2/(9K),
||R-R_(K,M)||_2 <= sqrt(8/K)+pi/M.                    (BFP3)
```

On the full base commutant `Z_K={S_K}'`, the minimum-norm inverse of
`1-Ad(R_(K,M))` off its fixed algebra has norm at most

```text
KM/4.                                                  (BFP4)
```

Thus both sources of arbitrarily small adjoint spectral gaps in an exact
finite-dimensional `BS(1,4)` skeleton--long base orbits and continuous
return-phase ratios--admit a quantified same-dimensional preconditioning.
