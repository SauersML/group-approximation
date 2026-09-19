---
rg: 2
id: torus-knot-k34-expander-pair-has-no-eigencorner
kind: claim
title: "An expander corona pair X^4 = Y^3 != 1 with no eigencorner: left-regular SL_2(F_p) generators twisted by a Lipschitz phase"
distinct_from:
  torus-knot-group-k34-has-central-eigencorners: that claim asserts an eigencorner for every pair; this one is an explicit pair with none, so it refutes that claim.
  commutant-projection-extraction: that asks for approximate eigencorners for every countable group and central element; this pair (H = K(3,4), eps = x^4) is a torsion-free one-relator counterexample to it, not a Kazhdan one.
  corona-commutant-growth-witness: that witness makes the relative commutant larger under compression; this one shows the relative commutant of an expander pair has no projection that sees the central phase.
  central-eigencorners-die-over-full-radical-quotients: that assumes an exact eigencorner and shows it is fixed; this shows no eigencorner has to exist, even for a residually finite group.
  bounded-rank-corners-excluded: that excludes corners of bounded rank for perfect or minimally almost periodic sources; this excludes corners of every rank, by a spectral gap, for a source with many characters.
artifacts:
  - experiments/torus-knot-expander-eigencorner-2026-09-17/check.py
  - experiments/torus-knot-expander-eigencorner-2026-09-17/output.txt
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`torus-knot-k34-expander-pair-has-no-eigencorner-proof`.  The only import is
Selberg's theorem, in the form of Lubotzky's Corollary 2.13 and
Proposition 1.11, quoted verbatim in the route.

## Statement

Let `p` run through the primes `p >= 5`.  Put `G_p = SL_2(F_p)` and
`k_p = |G_p| = p(p^2 - 1)`.  Let `Q = prod_p M_(k_p) / (+)_p M_(k_p)`.

- `S = [[0,-1],[1,0]]` and `B = (ST)^2`, where `T = [[1,1],[0,1]]`.  In
  `SL_2(Z)` these satisfy `S^4 = B^3 = I`, and they generate `SL_2(Z)`.
- `alpha_p` and `beta_p` are the left-regular permutation unitaries of `S`
  and `B` on `l^2(G_p)`.
- `|g|` is the word length of `g in G_p` for `Sigma = {S^(±1), B^(±1)}`.
  Put `R_p = floor(log_4(k_p) / 2)` and
  `phi_p(g) = pi · max(0, 1 - |g| / R_p)`.
- `D_p = diag(exp(i phi_p / 12))`.  Put `X_p = D_p^3 alpha_p` and
  `Y_p = D_p^4 beta_p`.

Then `X = [(X_p)]` and `Y = [(Y_p)]` are unitaries of `Q` with

```text
X^4 = Y^3 = u := [(D_p^12)],        ||u - 1|| = 2,
```

so `x -> X`, `y -> Y` is a corona representation `Theta` of
`K(3,4) = <x, y | x^4 = y^3>` that moves the central element `x^4`.  But
**there is no nonzero projection `P in {X, Y}' ∩ Q` and no `lambda != 1`
with `u P = lambda P`.**

In the matrix form of `torus-knot-group-k34-has-central-eigencorners`:
`||X_p^4 - Y_p^3|| -> 0` and `||X_p^4 - 1|| -> 2`, yet no projections `P_p`
with `limsup ||P_p|| = 1`, `||[P_p, X_p]|| + ||[P_p, Y_p]|| -> 0` and
`||(X_p^4 - lambda) P_p|| -> 0` for some `lambda != 1` exist.

## What this changes

1. **`torus-knot-group-k34-has-central-eigencorners` is false.**  This pair
   is a counterexample to it.
2. **`K(3,4)` is not matricially stable.**  This is
   `torus-knot-group-k34-is-not-matricially-stable`, which combines this
   pair with `matricially-stable-groups-have-central-eigencorners`.  It
   refutes `torus-knot-group-k34-is-matricially-stable`.  Every rational
   obstruction vanishes here, since `H^2(K(3,4); Z) = 0`.  So the obstruction
   is not cohomological.  It is a uniform spectral gap in the quotient
   `K/<x^4> = Z/4 * Z/3`, and it contrasts with
   `torus-knot-groups-are-rq-stable`, where padding by finite-quotient
   representations is allowed.
3. **`commutant-projection-extraction` is false, and the witness is not
   Kazhdan.**  Take `H = K(3,4)` and `eps = x^4`.  `B = Theta(H)' ∩ Q` has
   no projection `q` with `||(Theta(eps) - lambda) q||` small for `lambda`
   away from `1`.  Indeed the diagonal lemma of
   `lifted-thompson-t-eigencorners-via-projection-extraction` would make such
   approximate corners into an exact one.  The group is torsion-free, one
   relator and residually finite.  Its node had guessed that Kazhdan sources
   were where it would fail.
4. **Class killed: "eigencorners for every pair of the cover".**  The torus
   knot route `lifted-thompson-t-eigencorners-via-torus-knot-cover` is dead,
   because its leaf is false.  The general projection-extraction route
   `lifted-thompson-t-eigencorners-via-projection-extraction` is dead for the
   same reason.
   - *Invariant:* a uniform Kazhdan constant for finite quotients of the
     central quotient, carrying a phase that is Lipschitz for the word
     metric.
   - *Death step:* every projection that commutes in operator norm with the
     expander action has, to within `O(eta / kappa)` in normalized
     Hilbert--Schmidt norm, the same diagonal as the uniform measure.  So
     every such corner sees `u` only through the trace `tau(|u - 1|^2)`, and
     that trace tends to `0`.
   The target `lifted-thompson-t-centre-has-commutant-eigencorners` survives.
   Its pairs must also satisfy the Thompson relators, and `T̄` has no finite
   quotients, so this construction cannot be pulled back to it.  Any proof
   of that target must now use the Thompson relators, and not only the
   torus-knot cover or a general extraction principle.

## Scope

- **Where the argument stops.**  It needs the central quotient to map onto a
  family of finite groups with a uniform Kazhdan constant.  For `pg = K(2,2)`
  the central quotient `Z/2 * Z/2` is amenable and has no such family, and
  the argument gives nothing.  That is consistent with Eilers--Shulman--Sørensen.
  This is the calibration case.
- **The trefoil.**  The same proof works verbatim for
  `K(2,3) = <x, y | x^2 = y^3> = B_3`.  It uses
  `PSL_2(Z) = Z/2 * Z/3 -> PSL_2(F_p)`, the unitaries `X = D^3 alpha` and
  `Y = D^2 beta`, and `D = diag(exp(i phi / 6))`.  A unitary representation
  of `PSL_2(F_p)` with no fixed vector is one of `SL_2(F_p)`, so the same
  Kazhdan constant applies.  This is recorded here and not given its own
  node.
- The Hilbert--Schmidt picture is the opposite one.  `tau(|u_p - 1|^2) -> 0`,
  so this pair is Hilbert--Schmidt close to a pair with `u = 1`.  That is
  consistent with Hadwin--Shulman's theorem that one-relator groups with
  non-trivial centre are II_1-factor stable.
