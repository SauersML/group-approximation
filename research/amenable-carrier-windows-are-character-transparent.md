---
rg: 2
id: amenable-carrier-windows-are-character-transparent
kind: claim
title: Every amenable-edge window of the HNN carrier admits enemy-shaped factorial hyperlinear characters
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  hnn-carrier-factorial-character-collapse: that asserts the GLOBAL collapse for the full carrier; this proves no subgroup-local window with amenable edge can witness it, locating the collapse's content irreducibly in the non-amenable assembly.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that records local realizability of the enemy's RESTRICTION DATA on amenable subgroups (plateau bullet); this strengthens realizability to full factorial hyperlinear characters of the local HNN window `<A, t>` satisfying every enemy hypothesis at once, killing the entire local-rigidity attack family rather than one probe.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that conditions on OPEN Connes embeddability of the nonamenable-stabilizer coset Bernoulli; this uses amenable-stabilizer wreaths, so the countermodels are unconditional.
---

Let `H` be the carrier over `Gamma = SL_3(Z[1/p])`, and for `A <= Gamma` let
`E_A = <A, t>_H ~= <A, t | [t, A cap Lambda] = 1>` (Britton).  Claim
(established; proof route): whenever the coset wreath
`W_A = (directsum_(A/(A cap Lambda)) C_2) rtimes A` is hyperlinear — so
unconditionally for every amenable `A`, and for sofic `A` with amenable edge
`A cap Lambda` by the recorded amenable-stabilizer soficity — there exist
factorial hyperlinear characters `sigma` of `E_A` with the enemy's exact
local shape: `sigma|_A` canonical (for the Heisenberg window `A = N`:
vanishing off the center with aperiodic central measure, per
`heisenberg-solenoid-trace-torsion-dichotomy`), yet
`sigma(t^-1 a^-1 t a) != 1` for some `a in A`.

Consequences.  (i) No unique-trace / character-rigidity / invariant-state
mechanism run inside a window with amenable edge can close the collapse;
the obstruction, if real, lives only in windows with NON-amenable
`A cap Lambda`.  (ii) Any such window either regenerates the whole group
(`<Lambda, A> = Gamma` once `A` holds two opposite `Z[1/p]`-root groups or
strictly contains `Lambda`) or bottoms out at the `SL_2`-corner window
`E_2 ~= <SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1>` — the RANK-ONE carrier.  The
window hierarchy therefore re-derives the CORE A capstone (all arithmetic
routes meet at rank one) by pure subgroup theory, independently of the
Kostant cusp computation.  (iii) Every p-divisible element of `H` is
elliptic (`ell(g^(p^n)) = p^n ell(g)`), so there are no mixed solenoidal
Heisenberg subgroups, and characters with `delta_e` vertex restriction
vanish on every elliptic element: the enemy's freedom is carried entirely
by hyperbolic (irreducibly multi-t-block) elements.
