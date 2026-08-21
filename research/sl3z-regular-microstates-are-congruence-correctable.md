---
rg: 2
id: sl3z-regular-microstates-are-congruence-correctable
kind: claim
title: Regular-trace microstates of the lattice can be replaced by genuine odd-congruence representations
distinct_from:
  character-rigidity-equals-hyperfinite-hs-stability: that establishes HYPERFINITE HS-stability of higher-rank lattices from character rigidity, which corrects only microstate sequences with amenable limit; this asks for correction of the regular-trace sequences, whose limit is the non-amenable L(SL_3(Z)) -- exactly the sector the hyperfinite theorem leaves open.
  sln-z-flexibly-hs-stable: that asks for flexible HS-stability of SL_n(Z) as a route to the goal through the stability theorem; this asks only for correctability of the Lambda-RESTRICTION of regular microstates to odd CONGRUENCE targets, consumes it through the Weyl sector theorem instead of the stability route, and tolerates projective correction (phases die by perfectness).
  iwahori-outlier-repair: that is the Dogon-Vigdorovich representation-variety outlier repair at the Iwahori endpoint for the S-arithmetic group; this is the lattice-only, congruence-target form, and either implies the other's role in this lane.
---

Claim: for every sequence of maps `sigma_m : SL_3(Z) -> U(d_m)` that
is asymptotically multiplicative in normalized Hilbert--Schmidt norm
with asymptotically regular trace (`tr sigma_m(lambda) -> 0`,
`lambda != e`), there are genuine representations (allowed:
projective representations) `rho_m` of `SL_3(Z)`, factoring through
congruence quotients `SL_3(Z/n_m)` with `n_m` odd, such that

```text
max over the generating set of || sigma_m(s) - rho_m(s) ||_2 -> 0
```

after a vanishing-proportion corner correction (flexible form
allowed).

By `odd-congruence-lambda-exact-sector-collapses` (whose mechanism
survives projectivization: the corrector evaluation gives `W` scalar,
which suffices), this claim IMPLIES the full collapse `(RC3)`, hence
the goal through `non-hyperlinear-from-sl3-relative-commutant-collapse`.

## Attempts

- **What is known on each side (source-verified against
  Dogon--Vigdorovich arXiv:2506.20843v2, 2026-08-21).**  (i) DV's
  default "Hilbert--Schmidt stable" (their Definition 1.2, after
  [BL20]) IS the flexible version this claim allows -- corner padding
  `D_n >= d_n` built in.  (ii) Their Theorem 1.6: for irreducible
  lattices with (T;FD) in center-free semisimple groups of real rank
  at least 2, hyperfinite HS-stability, character rigidity,
  (T;FD)_rob and finite-dimensional approximability of characters
  are all equivalent; since character rigidity is KNOWN for
  non-uniform higher-rank lattices (their citations [DGG+25, PT16]),
  `SL_n(Z)` for `n >= 3` is UNCONDITIONALLY hyperfinitely HS-stable:
  sequences with amenable ultraproduct trace are correctable, and
  "character rigidity is witnessed on a finitary level."  This claim
  is exactly the non-amenable complement (the regular trace generates
  `L(SL_n(Z))`).  (iii) This claim is the higher-rank lattice
  analogue of DV's Question 1.4 (the Iwahori question: are
  representations of `SL_2(Z)` almost factoring through odd
  congruence quotients close to congruence representations?).  The
  structural difference is decisive: DV's route to the goal
  (Theorem 1.3 + Corollary 1.5) consumes such a statement at `SL_2`
  ONLY, because it needs a central `Z`-extension with infinite
  `pi_1(G(R))`; the Weyl-sector route
  (`sl3-collapse-from-congruence-correctability`) consumes the same
  species of statement at any `n >= 3` with NO central extension --
  the rank-two Weyl evaluation replaces the extension mechanism
  entirely.  (iv) The known instability results for (T) groups cited
  by DV ([ISW20], [Dog23]) proceed through central-extension
  deformations, i.e. through unbounded 2-cocycles; in the stable
  range `H_2(SL_n(Z))` is the finite `K_2(Z) = Z/2`, so no published
  obstruction applies to the regular-sector correctability of the
  lattice itself: the hole is genuinely open in BOTH directions,
  exactly like DV's Question 1.4, of which it is the deep-rank
  sibling.
- **Why the correction may exist here when full stability might
  fail.**  The known instability mechanisms for higher-rank groups
  are scalar-2-cocycle/central-extension obstructions (Deligne type,
  live for `Sp`), which vanish in the projective category the claim
  allows; and the claim does not require the corrected family to be
  close in operator norm or to preserve multiplicities -- only
  normalized-HS proximity of finitely many generators with flexible
  corners.  No known obstruction survives all three relaxations for
  `SL_3(Z)`.
- **Falsification gate.**  If `SL_3(Z)` has genuinely non-correctable
  regular-trace microstates even projectively-flexibly, this claim is
  false; the sector theorem still stands, and the enemy of `(RC3)`
  must USE such microstates -- so either way the goal lane sharpens:
  a proof here finishes `(RC3)`; a refutation produces the first
  explicit non-correctable microstate family of a higher-rank
  lattice, itself a major structure result pointing at where the
  hyperlinear enemy lives.
- **State of the cohomological stability art (2026-08-21 scout,
  source-verified).**  (i) De Chiffre--Glebsky--Lubotzky--Thom
  (Forum Math. Sigma 8, 2020; arXiv:1711.10238) prove stability from
  degree-2 cohomology vanishing -- but in the UNNORMALIZED Frobenius
  metric; the normalized-HS analogue of the criterion, which is what
  this claim needs, has no published counterpart, and this norm gap
  is exactly why the chain "vanishing implies stability implies
  collapse" does not already close the field.  (ii) Bader--Sauer
  (arXiv:2308.06517) prove SL_N(Z) has higher Kazhdan property
  (T_(N-2)): REDUCED unitary cohomology vanishes in degrees up to
  N - 2 for representations without invariant vectors -- the
  real-place Garland analogue; so degree-2 vanishing holds for
  N >= 4, and it is sharp (non-vanishing in degree N - 1 for
  N in {3,4}: arXiv:2410.22310).  Two upgrades are missing for the
  DGLT-style route even unnormalized: reduced-to-unreduced (a
  quantitative modulus, i.e. a degree-2 cohomological-Laplacian
  spectral gap -- the certified-SOS program of Kaluba--Mizerka--Nowak,
  arXiv:2207.02783, arXiv:2404.10287, currently degree 1 at SL_3 and
  inducing results) and invariant-vector coefficients.  (iii)
  arXiv:2512.09180 shows property (T_2) is NOT necessary for
  Frobenius stability (stable f.p. examples far from (T_2)), so the
  normalized-HS question is not cohomologically determined either
  way.  CONSEQUENCE for the lane: at N >= 4 the degree-2 vanishing
  machinery exists in reduced unnormalized form, so instantiating
  the whole Weyl-sector lane at the pair (SL_4(Z), SL_4(Z[1/p])) or
  (SL_5, ...) -- the sector theorem's mechanism is rank >= 2 and
  applies verbatim -- puts this hole in the only place where a
  cohomological attack has existing infrastructure; a normalized-HS
  DGLT criterion at N >= 4 would close the goal outright.
- **Quantitative interface.**  Any correction modulus here composes
  with the exact evaluation `W = 1` and needs no uniformity beyond
  the generating set: the Weyl relations are finitely many fixed
  words, so an `eta`-correction gives `(RC3)` up to `C eta` and the
  ultraproduct closes the gap.  This is a much lighter demand than
  the dimension-free moduli the transfer inequalities require.
