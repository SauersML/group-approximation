---
rg: 2
id: sl3-z-weakly-ucp-stable
kind: claim
title: SL_3(Z) is weakly ucp-stable, equivalently flexibly HS-stable on hyperlinear approximations
distinct_from:
  sln-z-flexibly-hs-stable: that asks for flexible HS-stability of SL_n(Z) for SOME n at least three and for ALL asymptotic homomorphisms; this is the n = 3 instance restricted to hyperlinear approximations (separating sequences), stated in Dogon's weak-ucp language — by kazhdan-weak-ucp-stability-is-flexible-stability the infinite-dimensional dilations add nothing for a Kazhdan group, so the only difference is the quantifier restriction, which is all the HNN mechanism uses.
  sl3z-regular-microstates-are-congruence-correctable: that asks to correct the lattice restriction of regular microstates to genuine ODD-congruence representations, for consumption by the Weyl-slot sector theorem; this asks for correction of every hyperlinear approximation to genuine representations of unrestricted level, for consumption by the HNN theorem over a thin co-dense subgroup, and is stated in Dogon's dilation language.
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

**Stakes.**  By `kazhdan-weak-ucp-stability-is-flexible-stability` this
claim is the same as flexible HS-stability of `SL_3(Z)` on hyperlinear
approximations, which is exactly what the HNN theorem consumes.  So
through `sln-z-thin-codense-tau-pair` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` it makes the literal
finitely presented group `< SL_3(Z), t | [t, a] = 1, [t, b] = 1 >`
non-hyperlinear (`non-hyperlinear-from-sl3-z-weak-ucp-stability`), with no
collapse or face input.  A second, now superseded, consumption confines
the p = 3 HNN microstates to the `Lambda`-exact face
(`kazhdan-subgroup-weak-ucp-exactifies-microstates`).

## Attempts

- **Not weaker than flexible stability for this group (2026-08-21).**
  The first framing of this node called weak ucp-stability "strictly
  weaker" than flexible HS-stability, quoting Dogon p. 4.  That is true in
  general (amenable non-RF groups separate them) but FALSE for Kazhdan
  groups on hyperlinear approximations:
  `kazhdan-weak-ucp-stability-is-flexible-stability` averages the
  Stinespring corner over a Kazhdan set into an exactly invariant
  finite-rank projection of the same normalized rank, so the dilation can
  be taken finite dimensional.  The claim is therefore an honest
  restatement of the `n = 3` flexible-stability hole on separating
  sequences, not a relaxation of it; its one genuine weakening relative to
  `sln-z-flexibly-hs-stable` is the quantifier (hyperlinear approximations
  only).
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
- **Source-verified literature boundary (2026-08-21 audit).**  Dogon
  arXiv:2211.10492, immediately after Theorem 1.6, states only the forward
  implications

  ```text
  flexible HS-stability => weak ucp-stability,
  LLP of C^*(Gamma)     => weak ucp-stability.            (WUS1)
  ```

  Ioana--Spaas--Wiersma arXiv:2006.01874, Corollary B, explicitly proves
  that `C^*(SL_n(Z))` fails LLP for every `n>=3`.  This failure is inherited
  from the subgroup `Z^2 rtimes SL_2(Z)`; it is not a converse to `(WUS1)`
  and therefore does NOT refute weak ucp-stability of `SL_3(Z)`.  The cited
  papers provide no subgroup-to-ambient permanence theorem for weak
  ucp-stability that would transport the subgroup obstruction.

  Dogon's actual property-`(T)` obstruction is Theorem 3.1: a sequence of
  nontrivial scalar `2`-cocycles converging pointwise to `1`, with every
  twisted group von Neumann algebra Connes embeddable, refutes weak
  ucp-stability.  No such sequence for `SL_3(Z)` is supplied by the LLP
  proof.  In particular the LLP obstruction cannot simply be relabelled as
  a weak-ucp obstruction.  Conversely, residual finiteness gives the
  factorization property and satisfies the NECESSARY conclusion of Dogon
  Proposition 1.11, but it constructs only one regular-trace ucp
  approximation and does not correct an arbitrary prescribed one.

  Hence no known LLP/property-`(T)` theorem in these sources establishes or
  refutes this claim.  The precise open sector is prescribed regular-type
  hyperlinear approximations: property `(T)` can turn an already supplied
  Stinespring corner into a nearby finite invariant corner (as in
  `kazhdan-subgroup-weak-ucp-exactification-proof`), but it does not produce
  the initial ucp approximation.
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
