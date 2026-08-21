---
rg: 2
id: arithmetic-hexagon-decoding-or-conductor-leakage
kind: claim
title: Arithmetic root microstates decode one A2 hexagon carrier or pay conductor leakage
distinct_from:
  six-edge-holonomy-energy-ledger-is-scale-free: that proves the analytic energy inequality after carriers and transitions are supplied; this is the matrix-coordinate extraction of those objects from growing congruence and periodic root spectra.
  affine-leavitt-boundary-shear-payment: that charges boundary expansion in the Leavitt coefficient system; this is the arithmetic SL3 root-depth version using the six-chamber Coxeter holonomy.
  same-orbit-closure: that prevents rectangular enlargement for paired Leavitt quotients; this permits enlargement but requires every escaped piece to descend in conductor depth and enter a fixed-depth mass recurrence.
---

OPEN.  Fix a depth `N`.  For canonical normalized-HS microstates of

```text
C=SL_3(Z) < A=SL_3(Z[1/2])
```

with the balanced commuting-conjugate lamp projections `P,Q`, decode for the
first `N` dyadic conductor layers:

1. six rounded Heisenberg chamber packets;
2. carrier projections `R_(k,w)` for the six Weyl chambers;
3. supported chamber transitions on their common surviving carrier; and
4. first-exit projections measuring failure of a transition to stay in that
   carrier,

so that for constants depending on `N` but not matrix dimension,

```text
sum_(k<N,w) edgeEnergy_(k,w)
  <= C_N (def(U)+sep_(F_N)(U)),                          (AHD1)
```

and escaped mass either is orthogonal first-exit mass or enters the next
shallower conductor layer.  There must be a fixed `kappa>0`, independent of
depth and dimension, for which the marked interior-overlap mass `m_k` obeys

```text
m_(k+1) <= (1-kappa)m_k
           + C_k (def(U)+sep_(F_N)(U)).                 (AHD2)
```

The mechanism required for `(AHD2)` is now finite and explicit.  On the mass
which does not leak, `six-edge-holonomy-energy-ledger-is-scale-free` makes a
role-rotating four-atom sector pay at least `m_k/8`; vanishing word energy
therefore forbids that sector.  On the leaked mass, the Weyl orbit of the
directionwise kernel-join packets generates the full principal layer two
levels down; the fixed `Lambda_0` property-T gap must charge or descend it.

Iteration gives

```text
m_N <= (1-kappa)^N m_0
       + C'_N (def(U)+sep_(F_N)(U)).                    (AHD3)
```

Constants `C'_N` may grow arbitrarily with `N`.  Taking the canonical
microstate limit first and `N->infinity` second is therefore sufficient for
the fixed-depth nonhyperlinearity criterion.

## Attempts

- **Fixed odd clock packets close.**  For every fixed odd quotient packet,
  finite-group exactification plus the literal six-edge holonomy gives the
  no-leak branch with a dimension-independent modulus; this is
  `six-chamber-a2-holonomy-closes-fixed-clock-sector`.
- **Growing periodic clocks do not break the ledger.**  Their local stability
  constants may deteriorate with period, but the six-edge telescoping and
  four-atom floor do not.  A countermodel must therefore hide in the carrier
  extraction or move mass between conductor levels, not in a long holonomy
  word.
- **Moving Haar bins do not extract the carrier.**  Keeping a single circle
  coordinate under doubling has order-one total PVM transport energy, while
  moving to the conjugate solenoid coordinate gives exact covariance but
  leaves the cross-chamber multiplicity gauges unrelated.  The exact coset
  Bernoulli model passes every such tracial root/PVM test while retaining
  overlap `1/4`; see
  `moving-solenoid-bins-do-not-close-gallery-multiplicity`.
- **Pairwise walls are insufficient.**  Exact regular wall rotations from
  `adjacent-a2-chambers-share-only-commuting-wall` satisfy every pairwise
  shared-root moment.  Closing the six-edge carrier, rather than improving
  one-wall rounding, is essential.
- **Edge rounding after exact band recovery is complete.**  On any band on
  which the two endpoint `SL_3(Z)` actions are genuine representations,
  `kazhdan-polar-rounding-produces-supported-gallery-edges` turns the raw
  almost intertwiner into an exact partial intertwiner.  Its source/target
  trace loss is at most `(eta/kappa)^2` and its HS displacement is at most
  `2 eta/kappa`, uniformly in dimension and multiplicity.  Thus property
  `(T)` solves the analytic edge-rounding step, but cannot be invoked before
  compatible genuine band representations have been extracted.
- **One selected corner is not easier to correct.**  Canonical mixed trace
  tests make every positive native four-atom/parahoric corner carry the
  regular lattice trace.  Moreover a correction theorem using only one
  approximately reducing selector would imply full regular-microstate
  correction for `SL_3(Z)` by tensoring an arbitrary microstate with one
  external bit; see
  `selected-corner-correction-contains-regular-correction`.
  The needed theorem must therefore correct the six corners and their
  transitions jointly, rather than exactifying them independently.
- **Even a flat six-corner corrector can keep overlap `1/4`.**  Reduction of
  the `A_2` coweight lattice modulo two gives a nonconstant affine corrector
  satisfying every inverse, Weyl, triangle, and closed-hexagon equation with
  zero holonomy; its finite lamp model retains independent half projections.
  See `coxeter-hexagon-admits-flat-affine-corrector`.  Thus the open decoder
  must use a mixed root outside each directional parahoric and charge the
  affine tail `(FAC10)` to conductor exit.  Raw or corrector hexagon closure
  alone is insufficient.
- **The actual parahoric atlas kills every abelian flat gauge.**  The toy
  affine escape uses substitute vector stabilizers.  On the true `42`-point
  atlas, the `C`-orbit of the signed triangle relation is an integral
  unimodular basis; hence every covariant commuting corrector collapses with
  a dimension-independent HS modulus.  See
  `actual-parahoric-triangle-kills-abelian-correctors`.  The remaining mixed
  tail is therefore genuinely nonabelian, not another conductor torus.
- **Periodic conductor plateaux pay a constant seam.**  A truncated dyadic
  shift makes every fixed root-depth test have squared defect `O(C_N/L)`,
  but independent root clocks fail the first adjacent-root Steinberg
  triangle with squared defect exactly `2`.  Replacing each chamber by an
  exact finite Chevalley packet merely moves this constant failure to the
  literal shared-root identities between adjacent chambers.  On arbitrary
  block-diagonal mixtures, target overlap `1/4` forces some one of the six
  wall defects to have square at least `1/3`; see
  `periodic-conductor-plateaux-pay-a-shared-root-seam`.  Thus the open enemy
  is non-block-diagonal rectangular multiplicity transport, not a long flat
  conductor band.
- **There is no residual nonabelian common-carrier gauge.**  If one supported
  corrector `Z` is invariant under the native parahoric and satisfies the
  ordered Weyl triangle, translating that triangle by `x_32(1)` and
  `x_21(1)` and cancelling its fixed factors shows that `Z` is also invariant
  under `x_23(1)` and `x_12(1)`.  These roots generate the whole actor, and
  the triangle then gives `Z=Z^2`.  The same calculation yields the
  dimension-free estimate `||Z-I||_2<=9 epsilon_tri+10 epsilon_D`; see
  `native-parahoric-triangle-kills-all-corrector-gauges`.  Thus the current
  hole is solely the common-carrier/rectangular-leakage extraction, not
  corrector holonomy after extraction.
- **Partial cancellation itself loses only first-exit mass.**  Left or right
  cancellation through a partial isometry is isometric on its actual source
  or range.  On a larger carrier `R`, the squared uncontrolled error is at
  most four times the trace of the missing source/range projection.  Applying
  this to the two translated native triangles gives a supported estimate
  `||R(Z-I)||_2^2 <= C edgeEnergy+C sum(firstExitMass)` with a fixed constant;
  see `partial-isometry-translate-cancel-charges-first-exit`.  Therefore the
  analytic cancellation endpoint no longer requires globally unitary
  correctors.  The open step is solely to extract the supported factors and
  route their actual support loss into the conductor recurrence.
- **Raw words canonically supply the partial transitions once bands exist.**
  For equal-trace band projections `P,Q`, polar-decompose `QUP`, where `U`
  is the raw actor word.  Its source loss, range loss, and squared polar
  displacement are all bounded by the single leakage
  `||(1-Q)UP||_2^2`.  Products of these polar transitions differ from the
  raw gallery word by at most the sum of square roots of the edge leakages;
  see `polar-compression-turns-band-mismatch-into-first-exit`.  Hence neither
  property-(T) exactification nor a separate common-gauge rounding theorem is
  needed after equal-trace conductor projections have been found.  The sole
  analytic gate is now constructing those projections and assigning their
  cross-band leakage to the depth recurrence.
- **Current unresolved step.**  Prove that separately rounded growing-period
  root packets either share enough multiplicity space for `(HEL11)` or that
  their mismatch is first-exit mass controlled by the two-level conductor
  join.  The descent itself is not a contraction for arbitrary isotypic
  weights (`weyl-kernel-joins-descend-two-levels-without-mass-contraction`),
  so the fixed `kappa` in `(AHD2)` must come from a matrix-only same-reservoir
  return or multiplicity payment, not from property `(T)` alone.  No
  dimension-independent proof of this extraction is currently in hand.
