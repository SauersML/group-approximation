---
rg: 2
id: parity-compressor-old-commutant-has-positive-density
kind: claim
title: Couple a Schur Reynolds carrier to positive density in the parity compressor's old commutant
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that gives positive density in a local finite-packet commutant difference; this must place that range inside the old compressor commutant rather than on an independent tensor factor.
  packet-kazhdan-commutant-placement-decouples: that is the exact tensor-product countermodel to bare commutation relations; this requires coefficient covariance which excludes it.
---

Modify the Toeplitz parity compressor by one fixed Schur--Clifford packet and
coefficient-covariance cell so that, on every marked microstate with
positive forbidden carrier mass, a spectral subspace `W` satisfies

```text
W <= low-commutator space of Lambda,
tr_ad(W) >= c q^2-C sqrt(E),                            (PCD1)
```

where `q` is the forbidden Hilbert mass.  The placement must visibly fail in
the tensor-decoupled representation of
`packet-kazhdan-commutant-placement-decouples`.

Then `parity-twist-copies-the-old-commutant-into-the-excess` sends `W` to an
almost orthogonal copy in the compressed low-commutator space, and
`property-t-hs-positive-density-commutant-no-growth` charges its density to
normalized-HS relator energy.  This would prove the parity compressor return
on every positive marked carrier.

There is now a shorter canonical-trace endpoint.  By
`canonical-marked-corner-kazhdan-density-vanishes`, the old low-commutator
space itself has vanishing adjoint density in every canonical marked
microstate.  Hence `(PCD1)` already contradicts hyperlinearity; the parity
copy and relative no-growth argument are optional downstream structure, not
part of the remaining hole.

## Attempts

- Declaring both packet subgroups to commute with the two Kazhdan copies is
  false: the packet may live on an independent tensor factor and retain its
  full Reynolds gap at zero covariance cost.
- Canonical scalar trace does not repair that tensor escape.
  `canonical-packet-traces-do-not-place-old-commutant-density` uses regular
  residual quotients of the old group tensored with the packet regular
  representation.  The whole product trace is canonical, forbidden packet
  mass and local Reynolds density stay constant, but the old low-commutator
  density is exactly `1/|Q_n|`.  Thus `(PCD1)` cannot follow directly from
  canonical word moments plus Schur identities; the added coefficient cell
  must visibly fail in this canonical dilution model.
- The local Schur theorem already supplies the density `c q^2`; the missing
  statement is an ordinary-word coefficient covariance that embeds its
  canonical three-generator Reynolds core into the compressor commutant.
- The covariance cannot be ordinary conjugacy of the whole nested packet.
  `nested-packet-reynolds-defect-is-orthogonal-to-old-commutant` shows that
  whenever `A<B` is transported with the full `B` subgroup into the old
  group, the transported range `R_A-R_B` is exactly orthogonal to the old
  commutant (and lies above the old adjoint Kazhdan gap).  Thus a live cell
  must transport only a partial/compressed coefficient or force the scalar
  overlap moment without conjugating the full packet table.
- Compressing all the way to one minimal packet idempotent does not by
  itself solve the problem.  In
  `minimal-packet-corner-overlap-has-irreducible-spectator-dilution`, the
  same exact packet table and the same carrier mass `q=1/n` have amplified
  corner overlap `1/n^3` when the multiplicity is trivial, but only
  `1/(n^3m^2)` when that multiplicity carries an irreducible old-group type
  of dimension `m`.  A single coefficient line has adjoint density only
  `1/(n^2m^2)` even before intersection.  Thus the partial-coefficient cell
  must authenticate the whole multiplicity action; local Schur relations or
  one favorable rank-one overlap cannot supply `(PCD1)`.
- A finite controlled-phase overgroup cannot impose that covariance on every
  selector sector.  The live implementation must use the one-sided Toeplitz
  coefficient action or a projective two-cell.
- Even genuine finite automorphism covariance is insufficient.
  `finite-normalizer-covariance-density-no-go`
  takes regular semidirect quotients in both normalizer directions: the
  packet keeps constant Hilbert mass and constant Reynolds density while the
  old low-commutator density is exactly `1/|Q_n|`.  Thus neither a packet
  acting by finite automorphisms on all named coefficients nor an old group
  acting by automorphisms on the packet prevents asymptotic decoupling.  The
  one-sided Toeplitz cell must use non-surjectivity in an essential way; its
  induced finite head action cannot be the missing estimate.
- The same regular-quotient proof absorbs every fixed finite-order projective
  normalizer table into its finite central extension.  Thus a projective
  two-cell is live only if its phase is tied to the genuinely one-sided
  coefficient transport; a standalone projective packet still has old
  density `1/|Q_n|`.
- `commutant-density-forces-bounded-type-mass` identifies the exact burden
  of `(PCD1)`: a lower bound `c_0q^2` on the old adjoint commutant forces
  linear-in-`q` Hilbert mass in old-`Lambda` irreducibles of degree
  `O(1/q)`.  Thus the missing cell is quantitatively a bounded-type compiler,
  not merely a way to make the local Reynolds projection invariant.
  Conversely, Wang finiteness for bounded-degree Kazhdan types shows that
  forcing a positive carrier into any fixed bounded-degree menu would suffice
  for positive commutant density.  So the exact representation-theoretic
  target is an equivalence: the Toeplitz covariance must compile the
  forbidden carrier into a bounded finite menu of old-`Lambda` types (the
  trivial type is not uniquely required).
- `kazhdan-bounded-types-form-central-summand` packages that entire finite
  menu into one central projection `p_<=K in C*_max(Lambda)`, with
  `tau_can(p_<=K)=0`.  Hence the missing estimate also has a scalar form:
  positive forbidden Schur mass must force positive `p_<=K` trace.  This is
  a useful falsification target for any proposed coefficient word, but it
  also confirms that `(PCD1)` already contains the trace-promotion step.
- There is no exact algebraic shortcut to that scalar promotion.
  `regular-trace-forbids-universal-bounded-type-placement` shows that every
  nonzero finite packet projection has positive regular trace, whereas the
  bounded-type Kazhdan projection vanishes in the same regular
  representation.  Thus no ordinary covariance relation can universally
  place the packet carrier under `p_<=K` while both subgroups embed.  The
  remaining theorem must be matrix-only and fail on the regular
  representation--which is precisely the sought nonhyperlinearity, not an
  algebraic coefficient-placement lemma.
- The proper Toeplitz transport itself has exact unbounded-type stationary
  exits.  `toeplitz-self-embedding-fixes-unbounded-congruence-types` sends
  `T` onto growing finite fields, where `sigma` becomes the identity, and
  uses the irreducible projective augmentation type of `SL_r(F_q)`.  These
  representations extend across the ascending HNN with stable letter one,
  have `p_<=K` mass zero for every fixed `K`, and have old adjoint commutant
  density tending to zero.  They also kill the Toeplitz head defect.  Thus
  non-surjectivity plus transport cannot by itself prove `(PCD1)`; the live
  matrix-only statement must quantitatively use positive forbidden-head
  mass to exclude precisely this congruence collapse.
