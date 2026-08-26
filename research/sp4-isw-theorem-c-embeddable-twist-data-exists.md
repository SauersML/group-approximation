---
rg: 2
id: sp4-isw-theorem-c-embeddable-twist-data-exists
kind: claim
title: The symplectic lattice admits Theorem C cocycle data with Connes-embeddable twisted crossed products
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the lifting hole; this is its ONLY surviving refutation mouth — establishing this claim refutes that one through the moreover clause of Ioana--Spaas--Wiersma Theorem C.
  isw-theorem-a-has-no-data-on-sp4-lattice: that closed the scalar Theorem A mechanism, which needs finite-dimensional realizability; this is the operator-valued Theorem C mechanism, which needs no realizability at all and instead pays an R^omega-embeddability toll.
  sp4-mod3-twisted-fibres-have-llp: that carries the property-(T)-versus-Connes-embedding stake on the mod-three twisted GROUP fibres of the Deligne cover; this carries the same stake structure on Maslov-twisted Bernoulli CROSSED PRODUCTS, a different family of algebras with classical parts.
  scalar-twisted-bernoulli-ce-iff-twisted-group-factor-ce: that proves the Bernoulli classical layer adds no Connes-embeddability obstruction for a constant scalar twist of a residually finite group; this still asks for the surviving Maslov-twisted group factors to be Connes embeddable.
---

OPEN CLAIM.  There exist an ergodic p.m.p. action
`Gamma = Sp_4(Z) ~> (X,mu)` and 2-cocycles
`c_n in Z^2(Gamma, L^0(X,T))` such that

```text
(a) c_n is not a 2-coboundary, for every n
    (restriction to Lambda = Gamma; any Lambda with sigma|Lambda
    ergodic works, relative (T) being automatic since Gamma is
    Kazhdan),
(b) ||c_n(g,h) - 1||_2 -> 0 for every g,h in Gamma,
(c) L^infty(X) x|_{sigma,c_n} Gamma embeds into R^omega
    for every n.                                              (TC1)
```

**What establishment yields** (Ioana--Spaas--Wiersma Theorem C,
arXiv:2006.01874, p. 3, source-verified 2026-08-21, quoted at the
statement level): with (a)+(b) alone, "`C^*(Gamma)` does not have the
LP.  Moreover, if the twisted crossed product von Neumann algebra
`L^infty(X) x|_{sigma,c_n} Gamma` embeds into `R^omega`, for every
`n`, then `C^*(Gamma)` does not have the LLP."  The LP conclusion is
ALREADY known for `Sp_4(Z)` (their Corollary E with Example 1.3(i):
`H^2(Gamma,R) != 0`), so only the LLP content is at stake: (TC1)
established would REFUTE `sp2g-z-full-c-star-algebra-has-llp` (stamp
`refuted_by:` there), extinguishing the `g = 2` LLP route to
non-hyperlinearity and closing the higher-rank (L)LP question of
Fournier-Facio--Willett negatively.  Failure of (c) on every candidate
family would instead produce a Connes-embedding-problem headline (see
Attempts).

**Why (a)+(b) are available — the wall is (c).**  The
scalar supply that Theorem A could not use (no finite-dimensional
realizability is required here) feeds Theorem C: `H^2(Gamma,R) = R`
(rank one, `sp4-fd-projective-multiplier-is-finite` Step 0), a real
cocycle `b` with `[b] != 0`, and `c_theta := exp(2 pi i theta b)` give
scalar cocycles with `|c_theta(g,h) - 1| -> 0` pointwise as
`theta -> 0` and classes that are nonzero and pairwise distinct for
`theta_n -> 0` avoiding the countable image of `H^2(Gamma,Z)`.  Viewed
as constant `L^0(T^Gamma,T)`-cocycles over the Bernoulli action, they
stay non-coboundaries by the embedding
`H^2(Gamma,T) + H^2(Gamma,ZGamma) -> H^2(Gamma,L^0(T^Gamma,T))`
recorded by ISW (p. 3, citing Jiang [Ji16] via Popa's cocycle
superrigidity).  More precisely,
`sp4-maslov-circle-survives-in-bernoulli-l0-cohomology` checks Jiang's
natural constant-cocycle map and establishes this packet.  ISW Remark 1.1 (p. 3)
frames the same frontier: LP for a property (T) group would force
`H^2(Gamma,L^0(X,T))` to be countable for every ergodic p.m.p. action,
and "not a single calculation of `H^2`" for a free ergodic action of a
property (T) group is available.

## Attempts

- **The cohomological half is complete.**
  `sp4-maslov-circle-survives-in-bernoulli-l0-cohomology` verifies at
  Jiang, Lemma 2.9 and Remark 2.10, that the relevant map is precisely the
  natural inclusion of constant scalar cocycles and is injective for a
  Bernoulli action of a property `(T)` group.  Thus the selected small
  nontrivial Maslov classes satisfy (a)+(b), with no remaining hedge.
- **The `ZGamma` feed is rationally dead; the circle is the live
  feed.**  Borel--Serre (as quoted in Brück--Patzt--Sroka,
  arXiv:2306.03180, abstract, source-verified 2026-08-21): `Sp_2n(Z)`
  is a virtual duality group of dimension `n^2` with the symplectic
  Steinberg module as dualizing module; so `vcd(Sp_4(Z)) = 4` and a
  torsion-free finite-index `Gamma'` has `H^2(Gamma',ZGamma') = 0`
  (duality, `2 != 4`).  Restriction to `Gamma'` of
  `H^2(Gamma,ZGamma)` lands in `H^2(Gamma',(ZGamma')^m) = 0`, and
  corestriction-restriction is multiplication by the index `m`, so
  `m . H^2(Gamma,ZGamma) = 0`: at most bounded torsion survives
  (exact group unrecorded).  Jiang's Bernoulli mechanism at `Sp_4(Z)`
  therefore runs on the `H^2(Gamma,T) = T x Hom(F,T)` summand — the
  Deligne circle — not on `ZGamma`-cohomology.
- **Gaussian/orthogonal route.**  ISW Remark 1.6 (p. 5): orthogonal
  representations `pi` with `H^2(Gamma,H_pi) != 0` would feed Gaussian
  actions IF the natural map `H^2(Gamma,L^2(X,R)) ->
  H^2(Gamma,L^0(X,R))` is injective for property (T) groups — an
  injectivity ISW state as open (they prove only the `H^1` analogue
  under spectral gap, their Theorem 7.4).  Even granted, this route
  faces the same wall (c).
- **Why (c) is uncharted in both directions.**  For the trivial
  cocycle, the Bernoulli crossed product of the residually finite
  `Sp_4(Z)` is expected embeddable through finite permutation models;
  but the theta-twists CANNOT be reached that way:
  `sp4-fd-projective-multiplier-is-finite` says only finitely many
  scalar classes of `Sp_4(Z)` are realizable through finite quotients,
  so for `theta` outside a finite set no congruence or
  finite-dimensional model respects the twist, and every standard
  sofic/profinite embeddability certificate is structurally
  unavailable.  Conversely, a NON-embeddable twist would be a von
  Neumann algebra attached to twisted ergodic data of a Kazhdan group
  failing Connes embeddability — the same famous stake recorded on
  `sp4-mod3-twisted-fibres-have-llp` for the mod-three group fibres,
  where no example is known.  Either resolution of (c) is a headline:
  embeddable twists refute the LLP hole; a non-embeddable twist
  settles the property (T) Connes-embedding problem.

- **The Bernoulli classical layer has now been removed from the toll.**
  `scalar-twisted-bernoulli-ce-iff-twisted-group-factor-ce` proves that for
  every constant scalar cocycle `c_theta` of the residually finite group
  `Sp_4(Z)`,

  ```text
  L^infty(T^Gamma) x|_(c_theta) Gamma is CE
      iff
  L_(c_theta)(Gamma) is CE.                              (TC2)
  ```

  The forward direction is the twisted group subalgebra.  In the reverse
  direction, tensor projective microstates of the twisted group factor with
  locally faithful finite-quotient Bernoulli permutation models; the first
  factor supplies the multiplier and kills nonidentity group traces, while
  the second supplies the cylinder-function moments and covariance.

  Consequently the operator-valued Theorem-C mouth is no longer a crossed-
  product permanence problem.  Once the constant Maslov classes are verified
  to survive in Bernoulli `L^0` cohomology, its only remaining analytic input
  is:

  ```text
  choose theta_n -> 0, [c_(theta_n)] != 0, with
  L_(c_(theta_n))(Sp_4(Z)) Connes embeddable for every n. (TC3)
  ```

  If one of these twisted group factors is non-CE, it already feeds
  `nonce-twisted-factor-gives-nonhyperlinear-group`; if all are CE, Theorem C
  refutes LLP for `C^*(Sp_4(Z))`.  Thus the classical Bernoulli action cannot
  distinguish the two outcomes.
