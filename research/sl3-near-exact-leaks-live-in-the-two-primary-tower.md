---
rg: 2
id: sl3-near-exact-leaks-live-in-the-two-primary-tower
kind: claim
title: SL3 near-exact-vertex leaks are confined to the two-primary congruence tower
distinct_from:
  odd-congruence-vertex-sector-admits-no-exact-leak: that is the SL_2 statement and needs the Serre amalgam plus Gerasimova-Shchepin vertex stability, and it leaves the enormous non-congruence representation wilderness of the virtually free vertex group uncovered; this is the SL_3 statement, where CSP plus superrigidity abolish the wilderness entirely, at the price of making near-exactness a hypothesis rather than a theorem.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that is the transfer inequality on exact representations of the whole group; this is the sector confinement for leak configurations whose VERTEX restriction is near-exact, using that inequality's mechanism through the odd factor of the level.
---

Let `Gamma = SL_3(Z[1/2])`, `Lambda = SL_3(Z)`, and let `(U_m, K_m)` be
microstates realizing an exact quasi-regular leak `(EQL1)` for this
pair.  Suppose the vertex restriction is near-exact: `U_m|_Lambda` is
within `eta_m -> 0` (normalized HS, on generators) of exact
finite-dimensional unitary representations `rho_m` of `Lambda`.  Then:

1. Each `rho_m` factors through a congruence quotient `SL_3(Z/N_m)` —
   unconditionally, by Margulis superrigidity (finite image of
   finite-dimensional unitary representations of the higher-rank
   lattice) and the congruence subgroup property of Bass--Milnor--Serre.
   There is NO non-congruence sector at `n = 3`, in stark contrast to
   the virtually free `SL_2(Z)`.
2. Write `N_m = 2^(a_m) m'` with `m'` odd and split
   `SL_3(Z/N_m) = SL_3(Z/2^(a_m)) x SL_3(Z/m')` by CRT.  On the odd
   factor, conjugation by `diag(2,1,2^(-1))` is defined and inner, the
   images of `Lambda` and `Gamma` coincide, and the doubled/(T)
   squeeze of the exact transfer gap forces the leak energy carried by
   the odd factor to vanish with `eta_m`.
3. Hence the entire leak profile concentrates on the `2`-primary
   factor: asymptotically, the enemy's commutant witness, its
   uncorrelated conjugates, and its whole `(EQL1)` structure live in
   the multiplicity data of the tower `SL_3(Z/2^a)` — the same
   two-adic solenoid direction as the SL_2 far sector, now with no
   alternative home.

Combined with the recorded uniform-outlier bound, the SL_3 enemy is
therefore EXACTLY one of two things: a uniform outlier from all exact
representations, or a two-primary congruence-tower configuration.  The
`SL_3` pair thus has the fully described enemy that `SL_2` cannot
offer, while also carrying property (T), the Hecke contraction, and no
amalgam construction surface: it is the correct battlefield for the
refutation, and this claim makes the reduction precise.

## Attempts

- Proved below by assembling established inputs; see the proof route.
  The one step that is a HYPOTHESIS here and a theorem at `SL_2` is
  vertex near-exactness: `SL_3(Z)` HS-stability is open (it is the
  Dogon--Vigdorovich program), so this claim describes the near-exact
  sector rather than eliminating the complementary outlier sector —
  matching the lane's standing division of the battlefield.
