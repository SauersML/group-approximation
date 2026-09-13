---
rg: 2
id: theorem-e-vertex-types-equidistribute-proof
kind: route
title: Transport isotypic projections through the exact intertwiner, collapse to unit type, and apply property (T) of SL_d(Z) on l^2 of the type set
target: theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits
requires:
  - vertex-rounding-alone-normalizes-each-theorem-e-model
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - vertex-rounding-reduces-ccr-to-commutant-excess
  - hs-block-gap-iff-liftable-masa-of-actor-commutant
artifacts:
  - research/artifacts/hs-masa-lift-positive-part3-2026-09-13.md
---

Full derivation: `research/artifacts/hs-masa-lift-positive-part3-2026-09-13.md`.

1. **Finite orbits (Section 1).** A unit-type type factors through `St_r(A_u)`, and the `x_i` have finite
   order `m` in `A_u`. So it factors through `L / (x^v - 1 : v in m Z^d)`, which is
   `SL_d(Z)`-invariant, with the action through `SL_d(Z/m)`. By
   `vertex-rounding-alone-normalizes-each-theorem-e-model`, the non-unit mass `tau(1 - P_n)` tends to
   0.
2. **Matching (Section 2).** Fix a nonnegative compressor `M = e_ij(1)`.
   - Item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess` gives intertwiners `v_n` from
     `pi_n|Lambda` to `Ad sigma_n(M) o pi_n o Ad M^(-1)`, with `||v_n - 1||_2 -> 0`.
   - Intertwiners carry isotypic projections to isotypic projections, so for any central coefficient
     vector `c` the transported central element moves by at most `2 ||v_n - 1||_2`.
   - Item 2 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
     `pi_n(Gamma) P_n = pi_n(Lambda) P_n`, identifies the `Lambda`-types on `P_n` with `Gamma`-types.
     The type restricting to `rho o Ad M^(-1)` is `M . rho`.
   - Random signs give summed matching. Trace invariance gives `||M_* p_n - p_n||_1 -> 0`.
3. **Property (T) on l^2(X) (Section 3).** `xi_n = f_n sqrt(p_n)` is almost invariant under a Kazhdan
   generating set `{e_ij(+-1)}`, by Hellinger control of `M_* p_n - p_n`. All orbits are finite, so
   the invariant projection is orbit averaging. Dividing by `E_orb sqrt(p_n)` gives an orbit function
   `g` with `|g| <= 1` and `||f_n - g||_(L^2(p_n)) -> 0`.
4. **Central lift (Section 4).**
   - Boundary for vertex generators: random signs and `||sigma_n(s) - pi_n(s)||_2 -> 0`.
   - Boundary for compressors: step 2 applied to orbit-sign unitaries.
   - Item 1 of `hs-block-gap-iff-liftable-masa-of-actor-commutant` gives `prod_U C_n <= Q`.
   - Step 3 gives the reverse containment for `Q cap prod_U Z(A_n)`.
5. **Multiplicity-free.** `A_n` is abelian on the multiplicity-one types, so `Q <= prod_U Z(A_n)` when
   the rest has vanishing trace. Then `Q = prod_U C_n`.
