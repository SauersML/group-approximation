---
rg: 2
id: sl3-z-weakly-ucp-stable
kind: claim
title: SL_3(Z) is weakly ucp-stable
distinct_from:
  sln-z-flexibly-hs-stable: that asks for FLEXIBLE HS-stability of SL_n(Z) for some n at least three (finite-dimensional genuine corrections) and consumes it through the HNN theorem with SL_n(Z) as the HOST; this asks for the strictly weaker weak ucp-stability (Dogon Def 1.5, infinite-dimensional dilations allowed) of the single lattice SL_3(Z) and consumes it as the SUBGROUP of the p = 3 pair through kazhdan-subgroup-weak-ucp-exactifies-microstates.
  sl3z-regular-microstates-are-congruence-correctable: that asks to correct the lattice restriction of regular microstates to genuine odd-congruence representations in the flexible (finite-dimensional) sense; this asks only that hyperlinear approximations of SL_3(Z) be corners of genuine representations on possibly infinite-dimensional spaces, and obtains the finite-dimensional exact correction afterwards from property (T).
---

OPEN CLAIM.  `SL_3(Z)` is weakly ucp-stable in the sense of Dogon
arXiv:2211.10492 Definition 1.5: for every hyperlinear approximation
`phi_n : SL_3(Z) -> U(H_n)` (asymptotically multiplicative in normalized
Hilbert--Schmidt norm, `liminf || phi_n(g) - 1 ||_2 >= sqrt 2` for
`g != e`) there are genuine unitary representations
`pi_n : SL_3(Z) -> U(H^_n)` on Hilbert spaces `H^_n supseteq H_n`, finite
or infinite dimensional, with
`|| phi_n(g) - P_n pi_n(g) P_n ||_(2, dim H_n) -> 0` for all `g`.

Equivalently (Dogon §2.4): every hyperlinear approximation of `SL_3(Z)`
is pointwise HS-asymptotic to the restriction to the group of a sequence
of ucp maps `C^*(SL_3(Z)) -> M_(d_n)`, i.e. to matrix-valued positive
definite functions on the group.

**Stakes.**  Through `kazhdan-subgroup-weak-ucp-exactifies-microstates`
this claim confines every would-be hyperlinear approximation of the p = 3
HNN group `< SL_3(Z[1/3]), t | [t, SL_3(Z)] = 1 >` (and of the coset
Bernoulli wreath `C_2 wr_(Gamma/Lambda) SL_3(Z[1/3])`) to the
`Lambda`-exact face of the collapse `(RC3-p3)`, so that
`lambda-exact-face-closes-at-p-three` finishes the goal
(`non-hyperlinear-from-p3-lambda-exact-face-and-weak-ucp`).

## Attempts

- **Implied by flexible HS-stability, not by residual finiteness.**
  Flexible HS-stability of `SL_3(Z)` (the `n = 3` case of
  `sln-z-flexibly-hs-stable`) implies this claim outright (Dogon p. 4).
  Residual finiteness plus (T) gives Kirchberg's factorization property
  (the regular trace is an amenable trace on `C^*(SL_3(Z))`), i.e. SOME
  sequence of ucp maps whose traces converge to `delta_e`; it says nothing
  about closeness to a GIVEN hyperlinear approximation, which is the
  content here.  Conversely Dogon Prop. 1.11 (hyperlinear + (T) + weakly
  ucp-stable implies residually finite) is consistent with the claim
  since `SL_3(Z)` is residually finite; Thom's hyperlinear non-RF (T)
  groups are the ones it excludes.
- **The LLP shortcut is closed.**  Ioana--Spaas--Wiersma Cor. 1.7: LLP of
  `C^*(Gamma)` implies weak ucp-stability; but as recorded in
  `no-published-unconditional-codense-stable-host`, the same authors show
  `C^*(SL_n(Z))` (`n >= 3`) fails LLP, so the claim cannot be imported
  from a lifting property.  It must be a genuine rigidity statement about
  almost-representations.
- **Hyperfinite sector is free, regular sector is the content.**  By
  Bekka's character rigidity and Dogon--Vigdorovich Thm 6.2, `SL_3(Z)` is
  hyperfinitely HS-stable: hyperlinear approximations whose limit
  character has amenable GNS are near genuine representations.  The
  hyperlinear approximations produced by the HNN/wreath microstates have
  limit character `delta_e` with GNS `L(SL_3(Z))`, non-amenable, so the
  known theorem does not apply; the claim is exactly the regular-type
  sector, the same sector as `sl3z-regular-microstates-are-congruence-correctable`
  but with infinite-dimensional dilations allowed.
- **Where a proof would have to live.**  A hyperlinear approximation
  defines, for each finite window, an almost-positive-definite
  matrix-valued kernel on the group; weak ucp-stability asks that it be
  HS-close to an honestly positive-definite one.  This is a
  Positivstellensatz-type question for the group (certificates of
  positivity modulo small HS error), not a cohomological one: the
  cohomological obstruction machinery of Ioana--Spaas--Wiersma and
  Dogon--Vigdorovich (second bounded cohomology, `Sp_2g` central
  extensions) attacks flexible HS-stability of groups WITH nontrivial
  `H^2`, which `SL_3(Z)` lacks (`abelian-lifting-obstruction-vanishes-for-sl-n-z`
  is the companion hole on the flexible side).  No attack on the ucp form
  is recorded anywhere in the graph; this node parks it.
