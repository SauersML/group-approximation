---
rg: 2
id: homogeneous-quotient-ce-outlier-proof
kind: route
title: The deep-tower lower bound on p-adic content contradicts the depth-free upper bound, so near-genuine microstates cannot exist
target: homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes
requires:
  - homogeneous-quotient-near-genuine-microstates-are-deep
  - p-divisible-lambda-exact-mass-vanishes-at-large-primes
---

Let `theta : M_p -> prod_U M_(d_n)` be a trace-preserving embedding and
`rho_n = theta o pi|_(SL_3(Z))` the restricted microstates, with defect
`epsilon_n -> 0` on a fixed finite generating set and its `h`-conjugates
(`h = diag(p,1,1/p)`).  `rho_n` is regular-type (the group unitaries have
the canonical trace, `tau(u_g) = 0` for `g != e`), so its limit character is
`delta_e` with non-amenable GNS `L(SL_3(Z))`; hyperfinite HS-stability does
not apply and the sequence is exactly of the type the outlier dichotomy
concerns.

Suppose, for contradiction, that along a subsequence `rho_n` is
`eta`-close (uniformly, on generators, normalized HS) to genuine
representations `rho'_n` for some fixed `eta` as small as we like after
passing to the tail.  Then `rho'_n` factors through `SL_3(Z/N_n)`,
`N_n = p^(D_n) m'_n`, and:

- **Lower bound on `p`-content (cells).**  The `K`-orbit indicators
  `1_(P_1), ..., 1_(P_r)` of `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`
  are `SL_3(Z)`-central and their equivariant cell family `{e_y}_(y in Y_1)`
  at the first congruence level has `|Y_1| = r |SL_3(Z/p)|`.  Step 2 of
  `homogeneous-quotient-deep-tower-proof` at `j = 0` gives
  `nu_0 = F(m'_n) <= 1 - 1/(8|Y_1|) + C_2 |Y_1| epsilon_n/kappa`, so
  `1 - nu_0 >= 1/(8|Y_1|) - o(1)`: a fixed positive amount of the microstate
  mass sits at positive `p`-level.  (This is where the crossed product,
  through its `K`-orbit cells, forces genuine `p`-adic content that a bare
  representation of `SL_3(Z)` need not have.)
- **Upper bound on `p`-content (depth-free).**
  `p-divisible-lambda-exact-mass-vanishes-at-large-primes` gives, at
  `p >= 11`, `a_p (1 - nu_0) <= C epsilon_n^2/kappa_0^2` with `a_p > 0`, so
  `1 - nu_0 -> 0`.

For large `n` the two bounds are contradictory: `1/(8|Y_1|) - o(1) <= 1 - nu_0 <= o(1)`.
Hence no subsequence of `rho_n` is near-genuine; `rho_n` is eventually an
outlier.  This proves the theorem, and the contrapositive is immediate:
if `SL_3(Z)` is weakly ucp-stable then `rho_n` is near-genuine (after
padding), contradicting the existence of the embedding, so `M_p` is not
Connes embeddable.
