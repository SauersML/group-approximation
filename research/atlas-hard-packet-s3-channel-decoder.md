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
  actual-hard-prefix-generates-s4-over-raw-s3: that closes the quotient-level finite S4 recovery for each hard prefix; this asks the actual relators to synchronize two extension decompositions and solve the multiplicity path-products.
  separated-channel-identities-retain-rectangular-escape: that proves finite carrier identities and coefficient equivariance cannot work as separated inputs; this requires genuinely mixed projected relator equations.
artifacts:
  - experiments/atlas-boundary-11-30.json
  - notes/TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md
  - notes/FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md
  - notes/TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md
  - notes/TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md
  - experiments/atlas_actual_hard_prefix_finite_packet.py
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

The finite carrier recovery is now established by
`actual-hard-prefix-generates-s4-over-raw-s3`: the cross-chart quotient word
itself generates `S4` with `K`, so that finite cell may be exactified and its
central channel projections used.  What remains part of this claim is the
unbounded multiplicity geometry between two such exact extensions and the
identification of its path maps with `(S3D2)`.

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

The obstruction is exact, not merely cautionary.
`separated-channel-identities-retain-rectangular-escape` tensors
any exact finite channel system with the doubled coefficient model.  Thus a
valid projected row must be mixed: the same operator equation must contain a
nontrivial finite carrier coefficient and one of the multiplicity transports
being solved.

There is an additional exact gauge count.  By
`s3-standard-operator-channel-has-fivefold-reduced-gauge`, an arbitrary
relative operator has five reduced sources in its diagonal-conjugation
standard channel, not three.  The three Racah intermediate channels and the
three `S4` extension labels are different spaces until the packet supplies an
intertwiner between them.  The live decomposition is therefore
`atlas-s3-decoder-authentication-and-minor-route`: authenticate the extension
triple first, then compute the literal minor.

The preferred authentication subroute is now
`atlas-a4-s3-hybrid-extension-authentication-route`.  It uses one nontrivial
`A4` line row and the trivial/sign `S3` rows, whose restriction fingerprint
on `2,3,3 epsilon` is diagonal.  This avoids trying to authenticate extension
labels from the five-source standard channel itself.  It does not remove the
later multiplication-minor gate.

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
- **Exactify the real prefix cell.** Insert the central idempotents of the
  quotient-level `S4` from
  `actual-hard-prefix-generates-s4-over-raw-s3`, not the classical-fold
  surrogate.  For two extensions, keep both decompositions of the shared
  `K` standard multiplicity space and retain their cross-products as
  operator unknowns.
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

## Equivalent sufficient matrix estimates

Let `epsilon(pi)` be the maximum normalized-HS defect of the fixed atlas
kernel rows.  It would suffice to prove, with a dimension-independent `C`,

```text
dist_2(G_n,A_(0,n)) <= C epsilon(pi_n),               (S3D3)
```

where the established coefficient calculation gives squared limiting
distance `15/128`.  A stronger sufficient form is

```text
sup_(V in U(A_n')) ||[V,F_n]||_2 <= C epsilon(pi_n),  (S3D4)
```

which contradicts `full-raw-packet-commutant-witness` and its asymptotic
squared commutator floor `3/8`.  Statements `(S3D3)` and `(S3D4)` are two
forms of the same mixed carrier--multiplicity synchronization gate; neither
is an abstract finite-group consequence.
