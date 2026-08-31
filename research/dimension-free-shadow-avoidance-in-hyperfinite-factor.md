---
rg: 2
id: dimension-free-shadow-avoidance-in-hyperfinite-factor
kind: claim
title: Small 2-norm elements admit norm-killing projections in the relative commutant, dimension-free
distinct_from:
  x2-local-afd-holds-at-rate-controlled-packets: that is the solved cell where the approximation rate pays for the dimension factors; this is the dimension-free strengthening whose truth would settle Problem X(2) positively for all packets.
  norm-folner-projections-for-hyperfinite-factor: that is the projection formulation of X(2) itself; this is a sufficient condition for it phrased inside the factor, isolating exactly what "how the bad directions sit relative to the finite-dimensional subfactor" must supply.
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

There is a function `δ₀(ε, j) > 0`, independent of `d`, such that: for
every finite-dimensional subfactor `M_d ⊂ R` with relative commutant
`R' = M_d' ∩ R`, and all `z_1,…,z_j ∈ R` with `‖z_i‖ ≤ 2` and
`‖z_i‖₂ ≤ δ₀(ε, j)`, there is a nonzero projection `s' ∈ R'` with

```text
‖z_i (1⊗s')‖ < ε  and  ‖(1⊗s') z_i‖ < ε   for all i.
```

By the argument of `x2-rate-controlled-local-afd-proof`, this
dimension-free form makes Popa's local-AFD criterion hold for EVERY
finite packet of `R` (apply it to the residues `z_i = y_i − E_M(y_i)`
of an arbitrarily good 2-norm approximation), so it implies
Problem X(2) affirmatively (`x2-via-dimension-free-shadow-avoidance`).

## Attempts

* **Entrywise spectral cuts pay `d` twice and die.**  Cutting each
  matrix corner `z^{kl}` over `R'` costs a union of `O(jd²)` spectral
  projections each of trace `O(dδ²/η²)`, and reassembling the matrix
  norm costs another factor `d` — total `δ ≲ ε d^{-5/2}`.  This is the
  solved rate-controlled cell, not the claim: hyperfiniteness gives no
  rate, so for generic packets `δ(d)` shrinks slower than any required
  power of `d`.
* **Black-box conversion is impossible** — the rank-`n` projection
  pair with `‖P−Q‖ = 1` and relative HS distance `√(2/n)` (recorded on
  `norm-folner-projections-for-hyperfinite-factor`) already lives in a
  relative-commutant picture; any proof must therefore use that the
  SAME `z_i` are being avoided by a projection from the commutant of a
  freely chosen subfactor — the choice of `M_d` adapted to `Z` is the
  unspent freedom.  Nothing forces `M_d` to be a CAR level.
* **One element, no matrix decomposition: TRUE.**  For `j = 1` and
  `M = ℂ` the spectral cut of `z*z` and `zz*` in `R` itself gives the
  statement with `δ₀ = ε²/2`-type bounds and no dimension anywhere.
  The claim is thus a genuine commutant-localization problem, not an
  approximation problem: the bad spectral subspaces live in `R`, and
  the needed projection must come from `R'`, whose "shadow" of a
  small-trace projection can be full — the failure mode is maximal
  entanglement of the bad directions with `M_d`.
* **Negative-side interaction.**  If the claim is FALSE, the failing
  configurations `(M_d, Z)` are themselves a new kind of witness
  candidate: packets whose bad directions are provably
  commutant-invisible.  No mechanism producing such configurations
  with a NON-quasidiagonality certificate is known — scale-free
  certificates (group marks) die in injective closures, and
  K-theoretic/Bott pairings dissolve because model scale is
  unquantified (see the denominator-freedom analysis in the artifact).
