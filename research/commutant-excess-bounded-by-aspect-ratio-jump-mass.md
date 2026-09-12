---
rg: 2
id: commutant-excess-bounded-by-aspect-ratio-jump-mass
kind: claim
title: The 2-norm excess of a subgroup commutant is controlled by the mass where the aspect ratio m/d jumps
distinct_from:
  commutant-no-growth: that is exact equality of the two commutants for genuine representations of the ambient group; this is a quantitative bound, for an arbitrary representation of the vertex and an arbitrary subgroup, on how far the subgroup commutant reaches outside the vertex commutant.
  invariant-size-collapse: that says a conjugation-invariant, refinement-sensitive size forbids strict compression; this names the refinement-sensitive observable m/d and bounds the 2-norm excess by the mass where it jumps.
  diagonal-leavitt-models-have-external-commutant-excess: that exhibits an extra commutant at distance one for diagonal Leavitt embeddings; this is a general upper bound on commutant excess in terms of aspect-ratio jumps, for every finite-dimensional representation.
artifacts:
  - research/artifacts/hs-scale-pinning-2026-09-12.md
---

**ESTABLISHED.** Let `pi` be a unitary representation of a group `Gamma` on `C^n`,
with normalized trace `tau`, and let `Lambda <= Gamma` be any subgroup. Put
`A = pi(Gamma)'` and `B = pi(Lambda)'`, so `A <= B`, and let `E_A` be the
trace-preserving conditional expectation onto `A`. Write:
- `pi = sum_i m_i rho_i`, with `rho_i` distinct irreducible of dimension `d_i`;
- `rho_i|Lambda = sum_j c_ij theta_j`, with `theta_j` distinct irreducible of dimension `e_j`;
- `m'_j = sum_i m_i c_ij`;
- `zeta_A = sum_i (m_i/d_i) z_i` and `zeta_B = sum_j (m'_j/e_j) w_j`, over the minimal
  central projections.

Then `zeta_A` and `zeta_B` commute, `zeta_B >= zeta_A`, and for every `0 < c < 1`

```text
sup { ||x - E_A x||_2 : x in B, ||x|| <= 1 }
   <=  4 tau( zeta_B >= (1+c) zeta_A )^(1/2)  +  2c.
```

**Consequences.**
- A macroscopic excess `delta > 2c` forces jump mass at least `((delta - 2c)/4)^2`.
- Merges (several `rho_i` restricting to one `theta_j`) and splits (`rho_i|Lambda` reducible)
  are the only ways the commutant can grow. `m/d` is monotone under both, and it strictly
  increases on the mass that carries the growth.
- With `vertex-rounding-reduces-ccr-to-commutant-excess`, (CCR) under vertex rounding
  becomes: the jump mass of `zeta_B/zeta_A` vanishes along `U` at every threshold.

Derivation: `commutant-excess-jump-mass-proof`.
