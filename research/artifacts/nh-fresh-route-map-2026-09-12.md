# Map of the routes into `non-hyperlinear-group`, 2026-09-12

Lane `ex-nh-fresh`. Read from main at `1754aa79d`, `ed270bac5` and `cd0f02cfd`. No `cairn check` was
run (RULES §1), so every status below is read from node text and route shapes, not from the kernel.

## 0. Counts and the invalidation keys

- 198 routes carry `target: non-hyperlinear-group`.
- 19 of them appear in some `invalidates:` list. A key kills a route only when the invalidating
  claim is established, so the 19 split three ways.

**Dead: the invalidator has a `requires: []` proof route that is not itself invalidated (6).**

| route | invalidator |
| --- | --- |
| `additive-index-transducer` | `additive-index-instability` |
| `exceptional-mixed-unilateral-shift-route` | `exceptional-mixed-pair-is-infinite-dihedral` |
| `invariant-size-argument` | `trace-blindness-sharpness` |
| `nonhyperlinear-from-extensive-index-defect` | `relator-only-hs-obstruction-has-trivial-model` |
| `nonhyperlinear-from-three-word-atlas-gap` | `atlas-three-word-gap-permutation-countermodel` |
| `separate-commutant-recovery` | `shifted-scale-recovery` |

**Pending: the invalidator is proved only through a conditional route (4).** The kernel decides.

| route | invalidator | its proof route needs |
| --- | --- | --- |
| `fanizza-wandering-dirichlet-return-route` | `uniform-clock-corner-is-not-a-reflection` | `uniform-clock-reflection-block-encodes-game-hamiltonian` |
| `nonhyperlinear-from-a4-plus-19243-classicalization` | `atlas-m2-refutes-five-global-a4-compilers` | nine atlas inputs |
| `nonhyperlinear-from-centralizer-product-classicalization` | `atlas-a4-gl5-packet-collision-screen` | `atlas-shortest-a4-triangle-packet`, `atlas-word-19243-is-kernel-relation` |
| `nonhyperlinear-from-coherent-heisenberg-module-decoder` | `coherent-heisenberg-decoder-is-marked-nonhyperlinearity` | `binary-leavitt-elementary-group-is-simple` |

**Not dead: the invalidator is open (9).**

- `non-hyperlinear-from-relative-commutant-collapse`, `nonhyperlinear-coset-wreath-from-commutant-collapse`,
  `sl3-coset-lamp-collapses-from-projective-transfer`: invalidator
  `sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`, OPEN. Its only route,
  `sl2-homogeneous-ce-via-global-treeing`, is itself invalidated by the established
  `sl2-homogeneous-action-is-not-treeable` (positive second L2-Betti number). The wiring is correct:
  that dead route does not fire.
- `non-hyperlinear-from-sl3-relative-commutant-collapse`, `nonhyperlinear-from-projective-trace-square-transfer`
  (and the third route above): invalidator `sl3-homogeneous-quotient-crossed-product-is-connes-embeddable`,
  OPEN. One route needs `sl3-noncompact-return-cocycle-spatializes`; the other is invalidated by
  `sl3-residual-kernel-spatialization-is-goal-equivalent`.
- `kt-pair-non-hyperlinear-commutant`: `kt-canonical-hs-normalization-fails` is OPEN with no route.
- `nonhyperlinear-coset-wreath-from-p3-collapse`, `nonhyperlinear-from-lamp-torsor-excess`:
  `coset-wreath-is-hyperlinear` is OPEN with no route.
- `nonhyperlinear-from-kun-thom-finitary-normalizer-obstruction`: `kun-thom-finitary-action-lifts-to-normalizer`
  has no route.

So 192 routes are live or undecided without the kernel. The most shared open inputs among the 179
routes with no `invalidates` key: `mipstar-bcs-tracial-nonru-exists` (14 routes),
`oracularizable-tracial-nonru-game-exists` (8), `atlas-steinberg-rank-five-translation` (8),
`canonical-profile-kleene-higman` (6). `leavitt-regular-atlas-hyperlinearity-criterion` (14) is an
established criterion, not a hole.

## 1. Families and their terminal cruxes

Ownership signals: commits in the last 8 hours by prefix (the 11:20 tree restore touches every file
and is ignored), plus this lane's brief.

### A. Kun--Thom wreath and the Theorem E vertex (owned)

`kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`, `kt-wreath-from-relative-actor-exactification`,
`kt-pair-non-hyperlinear-rigidity`, `kt-pair-non-hyperlinear-commutant`,
`nonhyperlinear-via-simple-lamp-action-recovery`, `nonhyperlinear-via-two-site-a5-center`,
`rigidity-route`, `scale-index-route`.
Crux: (H1) of `hs-stable-vertex-rounding-for-every-model` (flexible HS stability of the higher-rank
Kazhdan vertex at G-extendable models); at group level `hyperlinear-groups-kill-rigid-compression-defects`,
a win--win with Question 3.4. Owned by live peers (vertex rounding, Laurent `K_i`).

### B. The binary Leavitt unit group `Q = L_(F_2)(1,2)^x` (owned by neighbors)

About 40 routes: the regular-atlas routes (`nonhyperlinear-from-a4-*`, `nonhyperlinear-from-wedderburn-*`,
`nonhyperlinear-directly-from-fixed-pi-*`, `nonhyperlinear-from-one-cut-atlas-extraction`,
`nonhyperlinear-from-rectangular-wedderburn-isometry`, `nonhyperlinear-from-strict-s3-energy-ceiling`,
`nonhyperlinear-from-packet-s3-energy-incompatibility`, `nonhyperlinear-via-pi-degree-reservoir-lock`,
`source-saturated-reynolds-checksum-proves-nonhyperlinear`), the Pauli-carrier atlas routes
(`nonhyperlinear-from-pauli-*`, `nonhyperlinear-from-supercritical-pauli-branching`,
`nonhyperlinear-from-fractional-pauli-pressure`, `nonhyperlinear-via-balanced-router-pauli-holonomy`,
`nonhyperlinear-via-separate-native-quarter-recovery`, `nonhyperlinear-from-atlas-spectral-shrinkage`,
`atlas-radius-nine-trace-separator-route`), `nonhyperlinear-from-leavitt-24k-gap`,
`nonhyperlinear-via-leavitt-singular-near-state`, `nonhyperlinear-from-binary-leavitt-bad-character`,
`nonhyperlinear-from-binary-leavitt-native-cross-gram`, `leavitt-steinberg-stable-branch`,
`kl-violation-refutes-hyperlinearity-route`, `nonhyperlinear-thompson-v-from-one-word-ceiling`,
`nonhyperlinear-from-leavitt-steinberg-carmichael-area`, `nonhyperlinear-via-affine-leavitt-*`,
`affine-leavitt-global-pvm-route-to-nonhyperlinear`, `nonhyperlinear-via-binary-schur-toeplitz-payment`,
`nonhyperlinear-via-schur-toeplitz-root-defect`, `nonhyperlinear-via-parity-compressor`,
`nonhyperlinear-via-schur-amplified-parity-compressor`, `mixed-relator-route`,
`nonhyperlinear-from-linear-energy-domination`, `nonhyperlinear-from-two-s3-covariance-collapse`,
`nonhyperlinear-directly-from-five-row-phase-lift`, `nonhyperlinear-six-relator-group-from-five-row-lift`.
Crux by established equivalences: `Q` is nonhyperlinear iff the Steinberg cover is HS stable
(`steinberg-hs-stability-equals-nonhyperlinearity`), iff the regular-A8 relative-unitary problem has a
uniform gap, iff uniform Kazhdan heat rounding holds for canonical embeddings (Alekseev--Thom Open
Problem 6.2(a)). Owned by `ex-q34-leavitt-hs`, the Gottschalk rank campaign and the
Kervaire--Laudenbach campaign.

### C. Games, BCS compilers, reverse Kleene, Higman embeddings (owned by `ex-nh-mipstar`)

About 70 routes: every route needing `mipstar-bcs-tracial-nonru-exists`,
`oracularizable-tracial-nonru-game-exists`, `perfect-zpc-irs-quantum-gap-game`,
`culf-mastel-oracular-2csp-perfect-gap-family`, `canonical-profile-kleene-higman` or
`mikaelian-explicit-higman-embedding`; the dimension-reported compilers, doubling tapes and Clifford
towers; `nonhyperlinear-from-hs-pcp-boone`, `bcv-effective-microstate-search-nonhyperlinear-route`,
`non-hyperlinear-from-computable-hs-dehn-modulus`, `non-hyperlinear-from-hyperlinear-recognition-undecidable`,
`random-relator-entropy-nonhyperlinear-route`, `non-hyperlinear-from-algebraic-envelope`,
`nonhyperlinear-from-algebraic-compact-action-envelope`, `nonhyperlinear-from-amenable-group-basis-sl3`.
Crux: groupify an explicit perfect-completeness or non-CE game gap. Explicitness is the recurring
obstacle: MIP*=RE supplies non-CE algebras non-constructively.

### D. Arithmetic co-dense pairs `SL_n(Z) < SL_n(Z[1/p])` (dormant, unowned)

`non-hyperlinear-from-hnn-over-sl2-z`, `non-hyperlinear-from-hnn-over-sln-z`,
`non-hyperlinear-from-hnn-over-codense-kazhdan`, `non-hyperlinear-from-pauli-lamplighter`,
`non-hyperlinear-from-exact-quasi-regular-leak`, `non-hyperlinear-from-non-relative-embeddability`,
`nonhyperlinear-from-sl3-non-relative-embeddability`, `non-hyperlinear-from-sl2-amalgamated-free-exclusion`,
`non-hyperlinear-from-sl3-amalgamated-free-exclusion`, `non-hyperlinear-from-sl3-double-swap`,
`non-hyperlinear-from-relative-commutant-collapse`, `non-hyperlinear-from-sl3-relative-commutant-collapse`,
`non-hyperlinear-from-p3-relative-commutant-collapse`, `non-hyperlinear-from-sl3-large-prime-collapse`,
`non-hyperlinear-from-sl5-relative-commutant-collapse`, `non-hyperlinear-from-sl3-z-weak-ucp-stability`,
`non-hyperlinear-from-explicit-sl3-commutant-transfer`, `non-hyperlinear-from-thin-sln-commutant-transfer`,
`non-hyperlinear-from-iwahori-unitary-commutant-transfer`, `nonhyperlinear-from-canonical-iwahori-projection-transfer`,
`iwahori-sector-closure`, `nonhyperlinear-from-projective-trace-square-transfer`,
`nonhyperlinear-from-native-commuting-involution-transfer`, `nonhyperlinear-from-regular-actor-second-fold-bias`,
`nonhyperlinear-from-sl3-regular-double-fold-collapse`, `nonhyperlinear-from-sl3-swap-fold-square-rigidity`,
`nonhyperlinear-from-sl3-positive-density-projective-fold`, `nonhyperlinear-coset-wreath-from-*`,
`sl3-coset-lamp-*`, `sl3-codense-lamp-higman-route`, `nonhyperlinear-from-arithmetic-star-packet-wall`.
Crux: `arithmetic-pair-is-not-relatively-embeddable`. For each pair it is equivalent to
nonhyperlinearity of the centralizer HNN group, the enlarged and plain doubles and the binary coset
wreath (`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`,
`relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`), and at `n = 2` also to
`relative-commutant-collapse-for-sl2-pair` and exact quasi-regular leak exclusion
(`arithmetic-hnn-nonhyperlinearity-equals-global-collapse`). All of these are OPEN. Both homogeneous
crossed products (S2H1), (SH1) are open in both directions; the natural positive attack on (S2H1),
a global treeing plus Brown--Dykema--Jung, is dead.

### E. Deligne's triple cover `E_3` of `Sp_4(Z)` (HS side dormant)

`nonhyperlinear-via-deligne-central-mark-collapse`, `non-hyperlinear-from-e3-fibre-llp`,
`non-hyperlinear-from-sp2g-flexible-hs-stability`, `non-hyperlinear-from-sp2g-llp`,
`nonhyperlinear-from-sp4-llp-maslov-dichotomy`, `nonhyperlinear-from-odd-maslov-fibre-llp`,
`non-hyperlinear-from-twisted-generator-liftability`.
Crux: (DCM1) of `deligne-central-mark-hs-collapse`, equivalent to nonhyperlinearity of `E_3`
(`deligne-sector-gap-is-exactly-nonhyperlinearity`). Character rigidity (Dogon--Glasner--Gorfine--
Hanany--Levit) leaves only central-regular sector traces. LLP of `C^*(Sp_4(Z))` is open both ways; the
scalar Ioana--Spaas--Wiersma surface is closed and only their operator-valued Theorem C remains. The
rank-metric side of `E_3` was worked today (`deligne-rank-*`); the HS side was last worked 2026-08-21.

### F. Lifting properties (dormant)

`non-hyperlinear-from-llp-non-rf-kazhdan`, `nonhyperlinear-from-proper-d-completion-llp`,
`nonhyperlinear-from-three-dimensional-hyperrigid-lp`, and the LLP routes of family E.
Crux: an LLP or LP certificate for one explicit C*-algebra of a non-residually-finite Kazhdan group,
or of a completion.

### G. Isolated starts

`km-regular-synchronization-forces-nonhyperlinear` (Caprace--Remy lattices, last worked 2026-08-23),
`nonhyperlinear-from-cdi-image-character-rigidity` (Chifan--Drimbe--Ioana image quotient, 2026-08-27),
`nonhyperlinear-via-fournier-facio-singular-near-state`, `non-hyperlinear-via-hs-stable-kazhdan-hyperbolic`,
`nonhyperlinear-via-hs-stable-fd-residual`, `non-hyperlinear-group-via-nonzero-schur-kernel`
(Kervaire--Laudenbach adjacent, 2026-09-11), `nonhyperlinear-from-atomic-lamp-collapse`,
`non-hyperlinear-from-hyperlinear-implies-sofic`, `nonhyperlinear-from-single-context-v4-exit-capacity`,
`localized-square-return-gives-nonhyperlinear`, `nonhyperlinear-from-unnamed-fixed-space`,
`nonhyperlinear-from-macroscopic-self-copy-excess`, `nonhyperlinear-from-marked-extensive-index-energy`,
`nonhyperlinear-from-cyclic-carrier-energy-stability`, `nonhyperlinear-from-matrix-only-cyclic-carrier-invariance`,
`nonhyperlinear-from-even-partial-swap-star`, `nonhyperlinear-from-marked-swap-star`,
`nonhyperlinear-from-self-similar-square-function-checksum`, `non-hyperlinear-from-hs-relator-defect-gap`,
`agent-*`, `center-chain-*`, `fanizza-single-holonomy-proper-corner-route`,
`finite-adaptive-tree-via-morita-trace`, `full-packet-bicommutant-route`, `pauli-binary-membership-route`.

## 2. What the families share

Each terminal crux is a statement about all normalized-HS models of one explicit group, and each is
equivalent to nonhyperlinearity of an explicit group built from it (A: the wreath; B: `Q`; D: the HNN
group; E: `E_3`; F: through Kirchberg's (T) plus factorization theorem). No family has an intermediate
input known to be strictly weaker than its own terminal group problem.

## 3. Calibration by the simple Kazhdan LEF group (peer result, unreviewed)

`simple-kazhdan-lef-group-from-minimal-subshift` (lane `ex-kazhdan-simple-hyperlinear`, OPEN pending
review) gives `S = EL_3(LC(X,F_q) ⋊ Z)/Z` for an infinite minimal subshift `X`. If it survives review,
`S` is sofic and has: property (T); simplicity; no nontrivial finite-dimensional representation; no
residual finiteness; no finite presentation; no factorization property; no LLP for `C^*(S)`; and no weak
ucp-stability, hence no flexible HS stability (Dogon, arXiv:2211.10492, Proposition 1.11, as recorded
in `research/artifacts/nonhyperlinear-conditional-routes-landscape.md`). It contains the UHF locally
finite group `∪_j SL_(3·2^j)(F_2)`, which `Q` also contains. For the period-doubling subshift its ring
satisfies `LC(X,F_2) ⋊ Z ≅ M_2(LC(X,F_2) ⋊ Z)` (companion artifact
`period-doubling-elementary-group-phase-extraction-2026-09-12.md`).

Consequence for families B and G: a proof that `Q`, a Kac--Moody lattice, or any simple Kazhdan group
is nonhyperlinear cannot rest on that list. For `Q` it must use what `S` lacks: a module compression
`R_R ≅ R_R ⊕ R_R` (no rank model), hence an infranormal Kazhdan pair with nontrivial rigid defect.
Ring-level self-similarity and the UHF core are present in `S`. This sharpens the input (ii)
discussion of `research/artifacts/two-root-identity-nonsofic-mechanism-2026-09-12.md`.

## 4. Unowned starts, ranked

1. **D at `n = 2`.** `G_2 = <SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>`, equivalently RCC for the dyadic pair.
   Open both ways. The treeing attack on (S2H1) is dead; the amalgamated-free Haar unitary of
   `hnn-hyperlinearity-is-amalgamated-free-haar-unitary` is the exact positive object.
2. **E, HS side.** (DCM1) with the central-regular classification; no HS work since August.
3. **G, Caprace--Remy synchronization.** The Kazhdan LEF calibration of §3 replaces the amenable LEF
   countermodel as the benchmark a synchronization proof must defeat.
