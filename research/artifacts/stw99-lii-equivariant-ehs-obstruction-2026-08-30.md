# STW LII: the equivariant EHS strategy is refuted; the sharp Blackadar test case

*2026-08-30 goal session.  Follows up the LII root
(`stw99-problem-lii-lift-actions-on-invariant`), whose Attempts had
isolated an "equivariant Effros--Handelman--Shen realization" as the
natural route to Blackadar's lifting question on simple AF algebras.*

## Theorem (established this wave)

`equivariant-ehs-fails-for-sign-involutions`: the dimension group
`(Z^3, {x + θy > 0} ∪ {0}, u = (1,0,0))`, `θ` irrational, with the
involution `α = diag(1,1,−1)` (flip the infinitesimal axis) is not an
equivariant limit of simplicial groups with involutions.  Obstruction:
`H^1(Z/2, G) = Z/2` from the sign summand, against `H^1`-triviality of
permutation modules plus continuity of `H^1` under filtered colimits.
Corollary: any order-two lift of `α` to the AF algebra `A_G` preserves
no exhausting finite-dimensional nest — forced Blackadar-exoticism.

## Where the obstruction lives

* It needs an infinitesimal (or otherwise sign-acted) direction: on a
  SIMPLE dimension group every order-automorphism... can still have
  sign summands?  For a simple dimension group with unique state `s`,
  an involution satisfies `s ∘ α = s` (uniqueness), so `1 − α` maps
  into `ker s` = infinitesimals; if the group has NO infinitesimals,
  `Z_sign` summands can only occur inside `ker s`... which is dense
  but torsion-free of possibly high rank — sign summands are NOT
  excluded (e.g. `G = Z[1/3] ⊕ Z` inside `R` with... `α` must
  preserve the cone `s > 0`; `α = id ⊕ (−1)` on `Z[1/3] ⊕ Z_infml`
  needs the second summand infinitesimal).  For simple dimension
  groups WITHOUT infinitesimals the obstruction can still appear when
  the state space has dimension ≥ 1 and `α` swaps... this is left
  open here; the recorded theorem uses the infinitesimal witness,
  which is the cheapest.
* Blackadar's original question allows ANY order-2 automorphism of the
  algebra; his CAR symmetry shows exotic lifts genuinely occur (its
  fixed-point algebra is not AF, so it fixes no nest).  On CAR,
  `K_0 = Z[1/2]` is uniquely 2-divisible, so ALL `H^*(Z/2, K_0)`
  vanish and the cohomological obstruction is invisible — consistent
  with his lift existing.  The `(Z^3, θ)` witness is the first
  recorded example where exoticism is FORCED by the invariant.

## What this changes for LII

The lifting problem for involutions now splits:

1. `H^1(Z/2, K_0) = 0` (e.g. uniquely 2-divisible `K_0`): the
   equivariant-EHS route is unobstructed and plausibly closable by
   Barlak--Szabo-style averaging inside `M_{2^∞}`-absorbing hulls —
   but note LII's UHF-stability theorem (CGSTW 9.14) already covers
   exactly the `M_{|G|^∞}`-absorbing case; the content is AF without
   UHF absorption.
2. `H^1(Z/2, K_0) ≠ 0`: any lift is exotic; a refutation of
   Blackadar's question should be attempted HERE, on the explicit
   `(Z^3, θ)` witness.  Candidate refutation invariant: for an
   order-two `β` lifting `α`, the Z/2-equivariant K-theory
   `K^{Z/2}_0(A_G) = K_0(A_G ⋊ Z/2)` sits in the standard six-term
   ladder; whether the sign action on the infinitesimal axis forces a
   torsion class incompatible with `A_G ⋊ Z/2` being... (crossed
   products of AF by Z/2 need not be AF, so no cheap contradiction) —
   recorded as the open follow-up: compute the possible
   `K_0(A_G ⋊ β Z/2)` for ALL hypothetical lifts via Izumi-style
   duality and look for an empty range.

## Status

One established claim + proof route; LII root updated.  This is a
refutation of a strategy plus a canonical test case, not yet a
resolution of LII or of Blackadar's question.
