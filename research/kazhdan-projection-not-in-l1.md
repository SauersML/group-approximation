---
rg: 2
id: kazhdan-projection-not-in-l1
kind: claim
title: The Kazhdan projection is not integrable, so averaging cannot reach the operator norm
distinct_from:
  invariant-size-collapse: That claim says a compression collapses wherever the ambient category has a conjugation-invariant monotone size; this one explains why the (T) averaging machinery, which is the other way one might force a collapse, is unavailable in the corona at all.
  hs-invisibility-inflation-no-go: That claim says Hilbert--Schmidt invisibility alone never contradicts an operator-norm statement; this one identifies the structural reason every (T) argument in this cluster produces a Hilbert--Schmidt statement in the first place.
  kazhdan-asymptotic-commutant-transport: That claim is the positive transport theorem obtained by moving to the adjoint corona; this one says why that move is forced.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Let `Gamma` be an infinite group with property (T) and `p` its Kazhdan
projection in `C*_max(Gamma)`.  Then `p` is **not** in the image of
`l^1(Gamma)`, and the random-walk averages `mu^{*n}`, which converge to `p` in
the `C*_max` norm, are not `l^1`-Cauchy.

Consequence.  An isometric action of `Gamma` on a Banach space `A` extends to
`l^1(Gamma)` and, absent a Hilbertian structure, to nothing larger; so the
fixed-point projection cannot be manufactured by averaging.  In the norm
matrix corona `Q` with its operator norm — where `Ad Theta` is an isometric
action and `Q` is not Hilbertian — the operator `Ad Theta(p)` is simply not
defined.  This is why every property-(T) argument in this cluster first moves
to the adjoint corona on Hilbert--Schmidt spaces, where the action *is*
unitary and `p` does act, and why each such argument therefore terminates in
the `2`-norm.

Scope, stated plainly: this closes averaging as a route to
`corona-commutant-no-growth`.  It says nothing against K-theoretic,
saturation, or stability arguments, which do not use `p`.
