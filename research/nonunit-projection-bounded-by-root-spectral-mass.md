---
rg: 2
id: nonunit-projection-bounded-by-root-spectral-mass
kind: claim
title: The non-unit constituents of a congruence representation of EL_r(F_q[x]) are controlled by one root subgroup's spectral mass
distinct_from:
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that bounds the commutant excess by tau(1 - P_n); this bounds tau(1 - P_n) itself by the mass of root-subgroup characters that are nontrivial on the non-unit factor.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open rounding statement; this is an unconditional estimate on genuine congruence representations that reduces its conclusion to a statement about one abelian spectral measure.
artifacts:
  - research/artifacts/nh-unit-type-rounding-2026-09-12.md
---

**ESTABLISHED.** Setup:
- `r >= 3`, and `π : EL_r(F_q[x_1..x_d]) -> U(N)` factors through `St_r(B)`, with `B = A_u × A_nu` a finite ring split into unit-type and non-unit local factors.
- `P` is the projection onto the constituents trivial on `St_r(A_nu)`.
- `μ` is the normalized spectral measure of `f -> π(e_12(f))` on characters of `(B, +)`.

Then

```text
τ(1 - P)  <=  r(r-1) · μ({χ : χ|A_nu ≠ 1}).
```

**Reading.** Unit-type rounding in `theorem-e-vertex-rounds-to-unit-type-representations` is
equivalent to vanishing, along `U`, of the root-spectral mass that is nontrivial on the non-unit factor.
Derivation: `nonunit-projection-root-mass-proof`.
