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

- **What is known on each side.**  Hyperfinite HS-stability of
  `SL_3(Z)` is in-graph (`character-rigidity-equals-hyperfinite-hs-
  stability`, via Peterson/Bekka character rigidity): sequences with
  amenable ultraproduct trace ARE correctable.  The regular trace
  generates the non-amenable `L(SL_3(Z))`, so this claim is exactly
  the non-hyperfinite complement -- the same frontier as the
  Dogon--Vigdorovich Iwahori program, now needed only for the
  lattice and only at congruence targets.
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
- **Quantitative interface.**  Any correction modulus here composes
  with the exact evaluation `W = 1` and needs no uniformity beyond
  the generating set: the Weyl relations are finitely many fixed
  words, so an `eta`-correction gives `(RC3)` up to `C eta` and the
  ultraproduct closes the gap.  This is a much lighter demand than
  the dimension-free moduli the transfer inequalities require.
