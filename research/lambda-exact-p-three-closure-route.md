---
rg: 2
id: lambda-exact-p-three-closure-route
kind: route
title: Assemble the coprime slot, the Kazhdan floor, flatness, and the Weil-Rao flux at p three
target: lambda-exact-face-closes-at-p-three
requires:
  - odd-congruence-lambda-exact-sector-collapses
  - lambda-exact-face-of-the-collapse-closes
  - two-power-sector-conjugator-dichotomy
---

The assembly is the five-step chain printed in the claim; this route
records where each step lives and the two steps proved here.

Steps 1-2 are the required in-graph theorems, both prime-generic:
the coprimality-only Weyl slot evaluation closes every level coprime
to `p`, and the Kazhdan-floor theorem (with its consolidation in the
dichotomy node) closes regular-type `p`-power and bounded-gauge
towers.  Step 3 is the shift-invariance/flatness addendum of the
floor node: surviving profiles are flat, and flat profiles place
their mass proportionally on the deep generic (oscillator) bands,
which dominate the congruence duals by orbit-method genericity.

Step 4 (proved here).  On an oscillator band the canonical transport
of the flat tower implements the `Ad(h)`-shift of the central
character on the Heisenberg radical of the `(1,2)`-parabolic; by
Stone--von Neumann uniqueness any two unitaries doing so differ by a
scalar, so the transport IS the finite Weil intertwiner up to the
scalar that the canonical multiplicity matching fixes.  The
composition flux of the `p`-scaling Weil operators is the Gauss-sum
quotient: the level-`p^2` quadratic sum collapses by the substitution
`x = u + p v` to `p . (a|p) . g_p(1)`, and `g_p(1)` is `sqrt(p)` or
`i sqrt(p)` according to `p mod 4` (classical), giving flux `-1`
exactly for `p = 3 (mod 4)` — the Weil--Rao identity
`gamma(a) gamma(b)/gamma(ab) = (a, b)_p` in finite shadow.  The
root-data pairing: `h = alpha_1-vee(p) alpha_2-vee(p)` and
`h' = alpha_2-vee(p)`, so the BLS/Matsumoto commutator exponent is
the off-diagonal Cartan entry and `<h, h'> = (p, p)^(+-1)`; the
symbol is `+-1`-valued, so every sign convention yields
`(p, p)_p = (-1 | p) = -1` at `p = 3 (mod 4)`.

Step 5 (proved here).  A band with nontrivial flux admits no
consistent family of transports, so any near-conjugator's mass on
such bands is bounded away from contributing (its restriction there
would trivialize the flux); a flat profile is required by Step 3 to
place a fixed positive fraction of mass on the obstructed bands,
which is a contradiction.  Hence no `Lambda`-exact enemy exists at
any level structure for `p = 3 (mod 4)`, which is the claim.
