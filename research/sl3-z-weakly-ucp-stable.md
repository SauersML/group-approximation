---
rg: 2
id: sl3-z-weakly-ucp-stable
kind: claim
title: SL_3(Z) is weakly ucp-stable, equivalently fully flexible HS-stable
distinct_from:
  sln-z-flexibly-hs-stable: that asks for full flexible HS-stability of SL_n(Z) for SOME n at least three; this is exactly its n = 3 instance, stated in Dogon's weak-ucp language and identified with the full version by residual-finite-regularization-removes-the-weak-ucp-quantifier plus property T.
  sl3z-regular-microstates-are-congruence-correctable: that refuted odd-level strengthening required every regular correction to land in an odd congruence quotient; this asks for unrestricted-level correction of every hyperlinear approximation and remains open.
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

**Stakes.**  By `kazhdan-weak-ucp-stability-is-flexible-stability` and
`residual-finite-regularization-removes-the-weak-ucp-quantifier`, this
claim is the same as full flexible HS-stability of `SL_3(Z)` for all
asymptotic representations.  The HNN theorem consumes only its restriction
to one separating sequence.  Thus
through `sln-z-thin-codense-tau-pair` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` it makes the literal
finitely presented group `< SL_3(Z), t | [t, a] = 1, [t, b] = 1 >`
non-hyperlinear (`non-hyperlinear-from-sl3-z-weak-ucp-stability`), with no
collapse or face input.  A second, now superseded, consumption confines
the p = 3 HNN microstates to the `Lambda`-exact face
(`kazhdan-subgroup-weak-ucp-exactifies-microstates`).

## Attempts

- **Moving subgroup induction has no index loss.**
  `moving-subgroup-schreier-correction-has-no-index-loss` improves the
  fixed-index outlier exclusion: exact subgroup holonomy and vanishing
  root-mean-square Schreier edge discrepancy correct the original lattice
  tuple with constants independent of the subgroup index.  The corrected
  invariant summand has relative dimension `1+O(beta^2)`, even if the
  induced ambient dimension is arbitrarily larger.  This removes the
  index itself as an analytic obstruction.  It does not produce the
  exact subgroup holonomy or bound the moving word-area ledger from
  defining-relator defect; those are the remaining requirements for using
  this construction on an arbitrary microstate.

- **Not weaker than full flexible stability for this group (superseded
  quantifier audit, 2026-08-26).**
  The first framing of this node called weak ucp-stability "strictly
  weaker" than flexible HS-stability, quoting Dogon p. 4.  That is true in
  general (amenable non-RF groups separate them) but FALSE for hyperlinear
  Kazhdan groups.  Kazhdan averaging makes the ucp dilation
  finite dimensional.  More importantly,
  `residual-finite-regularization-removes-the-weak-ucp-quantifier` tensors
  an arbitrary asymptotic representation with exact regular congruence
  packets and untensors any ucp correction with constant one in normalized
  HS norm.  Thus this claim is the full `n = 3` flexible-stability hole;
  neither dilation nor input quantifier is a genuine relaxation.
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
  almost-representations.  Passing to the reduced algebra does not rescue
  this plan.  `sl3-reduced-group-cstar-has-no-llp` applies the
  regular-representation LLP obstruction to the residually finite,
  nonamenable lattice and proves that `C^*_r(SL_3(Z))` also fails LLP.  The
  corresponding dead route and refutation edge are recorded as
  `sl3-weak-ucp-via-reduced-llp`.
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
  refutes this claim.  Prescribed regular-type hyperlinear approximations
  remain a complete test class, but only because the exact regularization
  theorem transports their correction back to arbitrary asymptotic
  representations.  Property `(T)` can turn an already supplied
  Stinespring corner into a nearby finite invariant corner (as in
  `kazhdan-subgroup-weak-ucp-exactification-proof`), but it does not produce
  the initial ucp approximation.
- **Hyperfinite sector is free, regular sector is the content.**  By
  Bekka's character rigidity and Dogon--Vigdorovich Thm 6.2, `SL_3(Z)` is
  hyperfinitely HS-stable: hyperlinear approximations whose limit
  character has amenable GNS are near genuine representations.  The
  hyperlinear approximations produced by the HNN/wreath microstates have
  limit character `delta_e` with GNS `L(SL_3(Z))`, non-amenable, so the
  known theorem does not apply.  The regular-type sector is nevertheless a
  complete test class for this claim by the tensor-regularization theorem;
  the explicit even-level countersequence refuting
  `sl3z-regular-microstates-are-congruence-correctable` is already exact and
  therefore does not obstruct this unrestricted claim.
- **The large-prime one-twist theorem is downstream, not an exactification
  theorem.**  `p-divisible-lambda-exact-mass-vanishes-at-large-primes`
  begins with a genuine finite-dimensional representation `rho'` of
  `SL_3(Z)` and compares the isotypic weights of `rho'|_(C_0)` with those of
  its single `Ad(Jh)`-twist.  Its diagonal/off-diagonal argument therefore
  eliminates every shallow, flat, and ultra-deep `p`-divisible tower only
  after the lattice tuple has been corrected to the genuine representation
  variety.  An arbitrary regular-type hyperlinear approximation has no such
  exact isotypic measure before correction.  Producing that correction is
  precisely the present weak-ucp/flexible-stability claim, so the one-twist
  theorem neither proves nor refutes this node and cannot be used
  circularly to remove its outlier sector.
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
- **Global adjoint temperedness is false even in the exact congruence model.**
  `canonical-congruence-adjoint-complement-is-not-tempered` embeds a fixed
  finite-quotient mean-zero Koopman representation into the adjoint
  complement of a residual-chain regular embedding.  Its finite-index kernel
  acts trivially, so Hulanicki's criterion forbids weak containment in the
  regular representation.  Thus exactness, CSP, factorization, and character
  rigidity cannot prove this claim by making the whole adjoint complement
  tempered.  The strictly narrower selected-vector lemma
  `tempered-selected-conjugation-vector-obeys-rcc` remains valid, but deriving
  its hypothesis for a lattice-fixed leak is already the HNN-specific
  no-spherical-leak problem.
