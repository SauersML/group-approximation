---
rg: 2
id: sl2-carrier-vanishing-branch-character-collapse
kind: claim
title: Vanishing-branch factorial hyperlinear characters of the rank-one carrier centralize the letter
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  hnn-carrier-factorial-character-collapse: that is the n >= 3 carrier claim with the regular-restriction hypothesis; this is the n = 2 carrier with the strictly weaker vanishing-off-center restriction hypothesis (needed because ergodic components only preserve the vanishing-branch shape), and by the corner-window route it IMPLIES the n >= 3 claim — the two are now ordered, not parallel.
  relative-commutant-collapse-for-sl2-pair: that is the operator form quantifying over every unitary of a matrix ultraproduct commutant with regular restricted trace; this quantifies over factorial hyperlinear characters of ONE countable group, the form character rigidity and charmenability speak, and it suffices for the SL_3 goal via the window reduction rather than via co-density of the SL_2 pair alone.
  no-exact-quasi-regular-leak: that excludes the single extreme exact profile `1_Lambda`; this quantifies over ALL vanishing-branch factorial enemies of the rank-one carrier, intermediate between the exact form and the full collapse.
---

Let `E_2 = < SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1 >`.  Claim (OPEN): every
factorial hyperlinear character `sigma` of `E_2` whose restriction to
`SL_2(Z[1/p])` vanishes off the center `{±I}` satisfies

    sigma(s^-1 g^-1 s g) = 1   for all g in SL_2(Z[1/p]).        (R1)

By `sl3-collapse-from-rank-one-corner-window`, (R1) implies the full n = 3
carrier collapse (FC1), hence (RC3), hence the goal.

## Attempts

- **Why this exact hypothesis.**  Ergodic components of the SL_3 enemy's
  corner-window restriction are factorial, hyperlinear (corner-of-
  ultraproduct + martingale + weak-* closedness of hyperlinear traces), and
  a.e. vanishing-branch on the corner by Peterson-Thom character rigidity of
  `SL_2(Z[1/p])` (arXiv:1303.4007, Thm 2.6: extremal characters factor
  through finite quotients or vanish off center) plus a congruence-escape
  averaging that kills the finite-quotient mass.  The hypothesis is exactly
  what survives decomposition; the regular-restriction form would be too
  strong to consume.
- **Countermodel ledger.**  The amenable-wreath transparency countermodels
  (`amenable-carrier-windows-are-character-transparent`) do NOT apply: the
  relevant wreath over `SL_2(Z[1/p])/SL_2(Z)` has non-amenable stabilizers,
  and its hyperlinearity is the Kun-Thom wall; a hyperlinear such wreath
  would refute (R1) (pull back the regular character), so (R1) and CE of
  that coset Bernoulli stand or fall together — the recorded pairing of
  `coset-bernoulli-ce-refutes-relative-commutant-collapse`, now at rank one
  in character form.
- **Falsification gate.**  If `E_2` is hyperlinear, run the reduction
  route's component argument on the central components `tau_omega` of
  `delta_e^(E_2)` (they satisfy `tau_omega(g_j) = 0` off the center and
  `tau_omega(s^-1 g^-1 s g) = 0` for `g notin SL_2(Z)`, since Britton keeps
  that word off `{±I}`): a positive measure of their ergodic components are
  vanishing-branch factorial hyperlinear characters violating (R1).  So (R1)
  asserts, inter alia, that the rank-one HNN
  carrier is not hyperlinear: this is a goal-reaching claim, and refuting it
  means EITHER exhibiting a hyperlinear vanishing-branch enemy (killing the
  whole character lane at rank one) OR proving `E_2` hyperlinear (redirecting
  the program), both informative.
- **Known consistent sectors.**  Finite-dimensional characters of `E_2` are
  letter-central by co-density of the pair
  (`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`), and are excluded by
  the vanishing hypothesis anyway.  Tree deformations pass through the enemy
  exactly as recorded for the n >= 3 carrier: the enemy respects the
  Bass-Serre geometry, so IPP/spectral-gap arguments see nothing.
- **Toolkit pointer.**  The subgroup `SL_2(Z[1/p])` here has character
  rigidity (PT) and property (tau); what is missing is any rigidity
  statement for characters of the HNN CARRIER over the pair — the same
  virgin territory the n >= 3 node records, now in the weakest form the
  program needs.  The two-adic tower / Iwahori far-sector machinery is the
  natural quantitative attack surface, since a vanishing-branch enemy's
  finite shadows are exactly the doubly-deep solenoid-Haar plateaus already
  charted.
