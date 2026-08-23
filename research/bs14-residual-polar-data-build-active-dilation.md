---
rg: 2
id: bs14-residual-polar-data-build-active-dilation
kind: claim
title: Two cubic residual polar data build the active flexible dilation
distinct_from:
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for the sharp global semigroup repair; this asks only for the weaker active/passive dilation sufficient for qualitative flexible stability.
  bs14-energy-threshold-active-passive-ledger: that starts from a known positive corner; this must construct the corner directly from a near-solution.
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that rules out invariant hulling; this requires a non-invariant joint Gram completion instead.
---

OPEN.  Let `(R,S)` be an exact finite-dimensional `BS(1,4)` core and let
`X` have normalized four-relator energy `e`.  Put

```text
D_1=(XS^2)^3-1,              D_2=(XRS)^3-1,
tau=e^(1/4),                 theta=c tau,             (RPD1)
```

and form the high singular spectral subspaces of `|D_1|,|D_2|` above
`theta`, together with their polar partial isometries and mutual principal-
angle decomposition.

Construct from these data, without an assumed ambient dilation, a split in
which the `R`-fixed active source part is dilated and the orthogonal active
part is corrected internally or discarded:

1. prove that the high-residual source component orthogonal to `Fix(R)` can
   be removed or internally corrected at `O(e^(1/8))` normalized-HS cost,
   without taking its possibly unbounded BS-invariant hull;
2. add at most `C e^(1/2)d` new trivial-BS dimensions for the remaining
   `R`-fixed source component;
3. build a joint source/two-exit Gram completion and an exact Iwahori tuple
   on the enlarged space;

so that its compression is within `O(e^(1/8))` normalized HS of the input
tuple.

## Attempts

- `bs14-energy-threshold-active-passive-ledger` proves exactly these rates
  when the input is already known to be a polar compression of a positive
  fixed corner.
- Transverse high-residual carriers recover the source by
  `two-cubic-residual-carriers-recover-the-deleted-source`; nearly parallel
  carriers are handled by the active/passive energy dichotomy, so a uniform
  angle is unnecessary.
- `bs14-residual-invariant-hull-has-unbounded-packet-loss` rules out the
  obvious construction: the BS-invariant hull of one rank-one source can be
  an entire unbounded packet.  The new dimensions must carry the trivial BS
  type and couple non-invariantly through one joint Gram completion.
- The remaining exact obstruction is integral rather than spectral: the two
  residual polar decompositions must be rounded to one common collection of
  source/exit cells with integer multiplicities.  Separate singular-value
  rounding of `D_1,D_2` does not ensure their cells use the same added
  dimensions or satisfy both cubic equations.
- **Inversion adds a typed linear constraint before network-flow
  integrality.**  `bs14-trivial-boundary-inversion-forces-r-fixed-source`
  proves that the neutral added dimensions are forced to carry the trivial
  BS character and every source map must satisfy

  ```text
  RB=B,                 AR=R^(-1)A.
  ```

  Thus an untyped CS cell whose source is not `R`-fixed cannot be repaired by
  adding one trivial line, regardless of integer rounding.  On a scalar
  packet this forces return phase `v=1` and selects its unique `R`-fixed
  orbit sum.  The remaining transportation problem is therefore over these
  typed fixed-source cells, together with the involution Gram equations
  `(TBI3)`, not over arbitrary carrier dimensions.
- The phrase "add trivial-BS dimensions" cannot cover a `v!=1` active
  source: `(TBI2)` makes its coupling block exactly zero.  The earlier
  formulation silently treated every high-residual carrier as dilatable and
  was therefore too strong at the cell level.  The statement above now
  separates the missing phase-off-one internal correction/discard estimate
  from the `v=1` dilation.
- Even on the fixed-source sector, this is not an ordinary bipartite
  transportation problem.  `bs14-two-exit-typed-transport-is-not-saturated`
  writes the necessary matrix as a three-partite three-uniform incidence
  matrix and exhibits a determinant-two, index-two hole.  It remains to
  prove native-support balancedness, pay such parity holes within the active
  ledger, or use the operator Gram equations to exclude them.
- **At fixed support, nonnormality is not the lasting obstruction; lattice
  charge is.**
  `three-way-cell-semigroups-have-conductor-but-unbounded-charge` proves
  that every finite cell semigroup has one conductor packet which repairs
  all integral margins in its cone and group lattice.  But it also gives
  moving three-way supports with lattice charges of exact order `n` for
  every `n`.  Thus fixed-level saturation holes cost only bounded absolute
  padding after charge vanishes, whereas no level-independent saturation
  multiplier or same-support padding theorem can remove moving lattice
  charge.  The native BS operator data must force the correct lattice or
  pay for support-changing cells.
- **Every authenticated neutral compression is already in the correct
  lattice, and its support change is energy-paid.**
  `neutral-boundary-compressions-have-zero-restriction-charge` writes the
  compressed BS core class as the restriction of the full exact endpoint
  minus copies of the extendible trivial boundary.  Its native lattice
  charge is therefore zero without any packet decomposition.  Under the
  positive-corner spectral hypothesis, the existing cubic identity also
  bounds the restoring boundary rank by its Frobenius energy.  Hence the
  moving-charge issue survives only before a dilation has been
  authenticated: the reverse polar-data construction must prove that an
  arbitrary near tuple belongs to this compression class.
- `bs14-native-cell-padding-preserves-lattice-charge` shows that the phrase
  "pay such a hole by padding" must permit a controlled **change of cell
  type**.  Same-support padding preserves the incidence-lattice coset, so
  the determinant-two example cannot be repaired by adjoining any number of
  its four native cells, even though doubling the whole margin vector
  integralizes it.  The remaining statement must authenticate
  support-enlarging cells (or perturb the rounded margins); a bounded
  saturation exponent alone is logically insufficient.
- `bs14-long-packet-monodromy-reset-creates-fixed-sources` supplies one exact
  support-enlarging operation.  On a length-`m` packet, distribute the
  inverse `m`th root of its return monodromy over all cyclic edges.  This
  keeps the BS relation exact, changes `R` by at most `pi/m` in packet-
  normalized HS norm, and turns the whole multiplicity space into
  `R`-fixed sources.  Hence all orbit lengths at least `M` can be reset at
  global cost `pi/M`.  What remains is short-packet localization and the
  rebuilding of one exact `X`; changing `R` alone only perturbs, rather than
  solves, the inversion and second cubic equations.
- A short/long staircase cannot compute and repair the `m<=M` native cell
  semigroup in isolation.  `bs14-native-cells-cross-every-length-cutoff`
  uses full even-Weil tuples with `ord_p(4)>M`: their monodromy-one BS core
  is a trivial length-one packet plus long packets, and the exact `X`
  necessarily couples the two with squared norm `1-1/p`.  Therefore the
  actual native support contains cross-threshold cells for every cutoff.
  One must authenticate the global cell first and only then charge its
  rank-one short source; separate fixed-level repair does not build `X`.
- `bs14-global-atoms-are-moving-congruence-restrictions` identifies the
  exact global cells.  Every exact finite-dimensional endpoint factors
  through an odd congruence quotient, so its BS restriction lies in the
  directed union of the restriction monoids of the finite quotient
  irreducibles.  This removes exact noncongruence representations from the
  problem but does not provide an approximate decoder: the quotient level
  moves, and existing uniform infinitesimal rigidity starts only after a
  congruence atom has already been identified.  The remaining polar-data
  theorem is precisely a moving-level congruence-atom authentication with
  energy-controlled compression boundary.
- **A regular authenticated core still does not select the global atom.**
  `cuspidal-redistribution-refutes-regular-core-orbit-basin` redistributes a
  positive-density family of cuspidal multiplicities in the regular
  representation of `PSL_2(F_p)`.  Those cuspidals have identical Borel
  restrictions, so the exact BS core remains the regular restriction and
  the global characters are still asymptotically canonical, while Selberg
  forces the new exact involution a fixed distance from the regular endpoint
  orbit.  This is not a flexible-repair counterexample because the
  redistributed tuple is exact.  It proves that the reverse construction
  must choose an adaptive global endpoint type; authenticating the core and
  retracting to a preselected regular-quotient orbit is false.
- `bs14-bounded-moments-cannot-extract-congruence-level` rules out the
  simplest authentication interface.  Deep regular congruence
  representations at distinct prime levels, amplified to the same
  dimension, agree exactly on every fixed finite family of normalized word
  or finite-support Hecke moments; their cubic residual polar data are both
  zero.  The active dilation must therefore recover a compatible endpoint
  without a fixed scalar level fingerprint, or use a conductor-dependent
  hierarchy whose complexity grows with the model.
- The level-agnostic character split is complete but stops at the regular
  face.  `bs14-character-split-leaves-only-the-regular-microstate-face`
  cuts any ultraproduct character into a hyperfinite mixture of finite
  congruence characters and the regular character.  Hyperfinite stability
  corrects the former without naming levels.  The latter has GNS algebra
  `L(PSL_2(Z[1/2]))` and is exactly the unresolved presentation-microstate
  problem.  Hence the polar ledger must solve regular-character correction;
  no further scalar character dichotomy is available or needed.
- On that regular face, `bs14-regular-character-forces-sublinear-fixed-source`
  gives a genuine new rank bound.  The spectral law of the infinite-order
  `R` is Haar, hence `dim Fix(R)=o(d)`; by `(TBI2)` every neutral boundary
  source block has rank `o(d)`.  More sharply, creating fixed density
  `alpha` by a same-space perturbation costs at least
  `Phi(alpha)=2alpha-(2/pi)sin(pi alpha)`.  This makes source replacement
  flexibly affordable but still does not identify the cross-threshold exits
  or build the exact `X`.
- `bs14-low-rank-boundary-surgery-preserves-the-regular-face` proves the
  forward operation once a boundary is exposed.  Cutting a rank-`r`
  boundary and replacing the compressed selfadjoint contraction by its sign
  preserves involution and inversion exactly, changes `X` on rank at most
  `r`, and leaves each cubic with rank at most `6r` and Frobenius norm
  `O(sqrt r)`.  For `r=o(d)` all bounded words move by `o(1)`.  Crucially,
  this also preserves the regular character, so the remainder is not
  hyperfinite; the reverse construction from two residual polar carriers
  remains the genuine missing step.
- `bs14-thresholded-newton-needs-coordinate-basin`
  records the exact active/passive Newton synthesis.  Threshold `theta`
  leaves high rank at most `ed/theta^2` and low residual operator norm at
  most `theta`.  The uniform infinitesimal inverse then integrates with a
  dimension-free HS bound **if** the generators are already in a fixed
  operator-norm tube of an exact congruence atom.  Small residual operator
  norm does not supply that coordinate tube, and deleting a residual's high
  singular matrix is not an integrable modification of `X`.  There is no
  tangent inverse blowup; the missing gate is global operator-norm basin
  entry after high-carrier realization.
- The last gauge-integration step is now exact rather than perturbative.
  If the polar-data construction authenticates an exact endpoint
  `(X_0,R,S)` on the realized carrier and aligns the input as

  ```text
  X=cX_0,                 [c,S]=0,
  ```

  then `same-core-involution-cubic-gauge-coercivity` yields

  ```text
  ||c-1||_2 <= ||X^2-1||_2+||(XS^2)^3-1||_2.
  ```

  Hence active/passive thresholding no longer has to integrate a Koopman
  equation for `c`.  Its irreducible task is to construct and authenticate
  the exact common carrier/core and enforce the commutant alignment.  The
  residual polar data alone do not imply either fact, and the second cubic
  remains essential to select the common endpoint rather than an
  independently rounded first-cubic baseline.
- **A selected cyclic source has an exact frequency price.**
  `bs14-source-mode-reset-has-exact-frequency-cost` shows that any one
  `R`-eigenmode on a simple length-`m` packet can be made the unique fixed
  source by the exact reset `R -> lambda^(-1)R`, at cost `|1-lambda|`.
  There is never room for two independent fixed sources on that packet.
  Hence the active construction may select and reconnect one source without
  taking its invariant hull, but it must pay high cyclic frequencies and
  duplicate packet multiplicity when more than one source is required.
  What is still missing is extraction of one common source-mode ledger from
  the two residual polar ranges with total frequency and duplication cost
  controlled by their Frobenius energy.
- **Every bounded-period target is now known to be finite.**
  `bounded-period-iwahori-quotients-are-finite` applies the S-arithmetic
  normal-subgroup theorem to the preconditioner's unipotent power row.  Thus
  finite-group flexible stability closes the short-support problem at each
  fixed level, including arbitrary multiplicity.  This does not by itself
  produce the required long/short staircase: the finite-group presentation
  radius can still decay faster than the `O(K^(-1/2))` bounded-cycle
  preconditioning error.  Quantizing return monodromy is unnecessary because
  `s^N=1` alone already makes the augmented Iwahori group finite.  The
  remaining analytic statement is uniform basin entry across these moving
  finite quotients, equivalently the reverse carrier authentication above.
