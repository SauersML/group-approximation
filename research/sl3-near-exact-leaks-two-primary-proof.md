---
rg: 2
id: sl3-near-exact-leaks-two-primary-proof
kind: route
title: CSP and superrigidity abolish the wilderness, CRT splits the level, the squeeze clears the odd factor
target: sl3-near-exact-leaks-live-in-the-two-primary-tower
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - sln-z-thin-codense-tau-pair
---

**Step 1 (no wilderness).**  A finite-dimensional unitary
representation of `SL_3(Z)` has finite image (Margulis superrigidity
for higher-rank lattices, homomorphisms to compact groups), and by the
congruence subgroup property (Bass--Milnor--Serre) every finite
quotient is a congruence quotient: `rho_m` factors through
`SL_3(Z/N_m)`.  These are the same imports already consumed by
`sln-z-thin-codense-tau-pair`.

**Step 2 (CRT split).**  `SL_3(Z/N) = SL_3(Z/2^a) x SL_3(Z/m')` for
`N = 2^a m'`, `m'` odd.  Decompose `rho_m = rho_2 tensor-sum rho_odd`
along central idempotents of the two factors; the splitting is by
EXACT central projections of the image group algebra, so it is
preserved by everything that commutes with the image, in particular by
the leak witness `K_m` up to the vertex error `eta_m`.

**Step 3 (odd factor cleared).**  On the odd factor, `2` is a unit:
conjugation by `diag(2,1,2^(-1)) mod m'` is inner in `SL_3(Z/m')`, the
images of `Lambda` and `Gamma` coincide there, and the uniform
trace-square transfer gap of
`exact-projective-codensity-has-a-uniform-trace-square-gap` (perfect
Kazhdan subgroup, property (T) constant) applies: any unitary
almost-commuting with the odd-factor image of `Lambda` has
trace-square energy at `h` controlled linearly, with dimension-free
constants.  The exact profile `(EQL1)` demands energy `1` at `h`;
therefore the mass that the leak carries through the odd factor is
`O(eta_m + defect)` and vanishes along the ultrafilter.

**Step 4 (concentration).**  Unitarity of `K_m` forces the surviving
mass onto the complementary central projection, i.e. onto the
`2`-primary factor `SL_3(Z/2^(a_m))`, whose multiplicity data is
exactly the two-adic congruence tower.  There conjugation by the
Hecke element is not an automorphism (2 is not a unit), the level
shifts, and the configuration is the `SL_3` form of the solenoid wall.
No other sector exists by Step 1.  QED under the near-exact-vertex
hypothesis, with all constants dimension-free.
