---
rg: 2
id: atlas-hard-packet-s3-channel-decoder
kind: claim
title: The full atlas hard packet exposes an invertible S3 channel decoder for the three Leavitt pairings
distinct_from:
  finite-window-decoder: that asks for the complete common-coordinate Leavitt decoder; this is the concrete sufficient rank gate obtained by projecting the literal hard packet into the localized S3 cell.
  atlas-two-s3-covariance-collapse: that asks for direct collapse of two fixed raw S3 covariance directions; this asks instead for the three common-coordinate pairing products used by the spectral Leavitt endpoint.
  regular-chart-wedderburn-coefficient-compiler: that compiles arbitrary products into finite path sums without proving a rank condition; this asks for a nonzero minor in the particular class-11/class-30 channel system.
  regular-subgroup-branching-is-hall-balanced: that rules out every bare type-incidence Hall argument; this retains the actual multiplicity-operator products and their recoupling coefficients.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out a universal algebraic Hall certificate valid in the exact factor model; this is a finite-multiplicity extraction statement and must preserve that category boundary.
artifacts:
  - experiments/atlas-boundary-11-30.json
  - notes/TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md
  - notes/FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md
  - notes/TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md
  - notes/TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md
---

Exactify the fixed raw packet

```text
K ~= S3,
H = (1 tensor M_1) + (epsilon tensor M_epsilon)
    + (sigma tensor M_sigma).                         (S3D1)
```

Resolve the literal class-11/class-30 hard-prefix, full interior, boundary,
and comb relations into `S3` matrix-coefficient channels.  Multiplication
must be compiled through the multiplicity-one Clebsch--Gordan maps, retaining
every input pair which feeds a common output channel.  The resulting finite
system has coefficients in `Q(sqrt(2))` and contains a fixed nonzero minor
whose solved unknowns are exactly the path products producing

```text
||R0^* W L0-W||_2 -> 0,
||R1^* W L1-W||_2 -> 0,
||R0^* W L1||_2   -> 0.                              (S3D2)
```

All arrows and `W` in `(S3D2)` act on one common finite multiplicity
coordinate.  The coefficient-to-defect estimate is dimension-free.

The cross-chart hard prefix is not assumed to generate an exact `S4` action
in the microstate.  Its classical-fold `S4` value supplies channel labels and
candidate coefficients only; recovering the corresponding multiplicity maps
from the relators is part of this claim.

## Boundary of the claim

Classes 11 and 30 by themselves cannot prove this statement.
`atlas-two-s3-covariance-collapse` records an exact regular-margin model in
which all 234 first-boundary words vanish while the raw `S3` copies remain
misaligned.  Therefore the live system must include a genuinely interior or
full-comb consequence.  A minor computed from the two stored boundary words
alone is not a valid certificate.

Nor is multiplicity-free fusion by itself enough: several input-channel
pairs can feed the same output.  The theorem is precisely that the literal
full packet separates enough of those sums to recover `(S3D2)`.

There is an additional exact gauge count.  By
`s3-standard-operator-channel-has-fivefold-reduced-gauge`, an arbitrary
relative operator has five reduced sources in its diagonal-conjugation
standard channel, not three.  The three Racah intermediate channels and the
three `S4` extension labels are different spaces until the packet supplies an
intertwiner between them.  The live decomposition is therefore
`atlas-s3-decoder-authentication-and-minor-route`: authenticate the extension
triple first, then compute the literal minor.

## Attempts

- **Compile the literal packet, not a surrogate.** Start from
  `experiments/atlas-boundary-11-30.json` and explicitly name every packet
  relator or normal-closure consequence which constrains the comb word.  The
  comb source word is an operator name, not itself an equation.  Record for every projected row its
  source word, bracketing, input channels, output channel, path monomial, and
  exact coefficient.
- **Use the three established transforms as rank candidates.** Search the
  resulting matrix over `Q(sqrt(2))` for the `F_sigma`, restriction, or
  central-overlap pattern from
  `s3-hard-cell-three-channel-data-is-nondegenerate`.  Their invertibility
  proves only that a decoder is available if the relators expose it.
- **Make the falsification gate exact.** If every minor involving the three
  path products in `(S3D2)` vanishes after all literal relations are included,
  record that rank failure and close this route as false.  Do not replace the
  missing rows with an assumed `S4` representation.
- **Respect the factor-model audit.** Any proposed implication must identify
  the finite-multiplicity selection step which prevents it from becoming a
  universal star-ideal identity in the exact infinite regular model.
- **Literature provenance, not an imported theorem.** Shun Xu,
  arXiv:2608.13872, motivates the multiplicity-one-channel/nonvanishing/small-
  determinant proof architecture.  The VOA theorem is not used here; the
  actual atlas rank statement remains entirely open and project-specific.
