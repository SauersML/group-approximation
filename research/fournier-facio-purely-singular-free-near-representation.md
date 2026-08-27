---
rg: 2
id: fournier-facio-purely-singular-free-near-representation
kind: claim
title: The Fournier--Facio group admits a purely singular essentially free amenable near representation
distinct_from:
  fournier-facio-hyperlinear-iff-singular-near: That proves this witness is equivalent to hyperlinearity; this is the unresolved existence assertion itself.
  wreath-amenable-near-representation: That asks for a witness for the Kun--Thom wreath; this concerns the separate torsion-free Fournier--Facio candidate.
---

For the finitely presented torsion-free Fournier--Facio group `G`, construct
a Hilbert space `H`, a purely singular invariant state `phi` on `B(H)`, and a
`phi`-near representation `pi:G -> U(H)` satisfying

```text
phi(pi(g))=0                    for every g != 1.
```

By `fournier-facio-hyperlinear-iff-singular-near`, this is exactly the
positive hyperlinearity branch for `G`, not an auxiliary permanence
condition.

## Attempts

The operator-norm and unnormalized-Frobenius models already in the graph do
not furnish the witness: their stability is degenerate asymptotic triviality,
whereas essential freeness requires the regular character.  A normal
invariant state is also impossible by the established minimal almost
periodicity/pure-singularity reduction.  The remaining construction must use
a genuinely singular finitely additive charge, and no such charge is presently
known for the full Fournier--Facio compression group.

Two broad singular-charge constructions are now excluded, not merely left
untested.  `fournier-facio-compression-coset-charge-impossible` kills every
induced or Banach-limit basis carrying an equivariant map to `G/Gamma`, since
the charge would push down to a forbidden invariant mean.
`fournier-facio-monomial-near-witness-impossible` kills every remaining
phase-twisted Schreier/permutation basis: forgetting phases would give an
essentially free amenable near action and hence soficity.  A positive witness
must therefore be both singular and genuinely non-Cartan, mixing basis
vectors on positive charge with no equivariant coarse coset factor.

The monomial part of this non-Cartan requirement survives passage to the
Calkin algebra.
`fournier-facio-compact-monomial-near-witness-impossible` shows that arbitrary
compact perturbations of arbitrary phase-twisted permutation actors add no
freedom: the singular charged state and all charged pointwise tests erase
them.  Hence a positive witness cannot be monomial modulo compacts, rather
than merely a compactly blurred Schreier model.  This does not exclude an
abstract Calkin normalizer which has no coherent monomial lifts.

The obstruction is actually larger than the compact ideal.
`fournier-facio-charge-null-monomial-perturbations-impossible` removes every
perturbation which vanishes in the charged column seminorm, even when it is
noncompact and has order-one norm on an infinite charge-null subspace.  A
positive construction must therefore put genuinely delocalized,
nonmonomial action on a set of **positive charge**; a charge-null non-Cartan
reservoir cannot carry the missing hyperlinearity witness.

Uniformly finite-dimensional delocalization is also insufficient.
`fournier-facio-bounded-block-near-witness-impossible` allows arbitrary
matrix-valued cocycles on a common charged block system and arbitrary
charge-null errors, but uniform recurrence in `U(m)` forces the underlying
block near action to be essentially free.  Hence any positive witness must
have unbounded block sizes on positive charge or genuinely overlapping
finite-band supports with no common bounded block decomposition.

For a common finite-block system, “unbounded” has a precise meaning.
`fournier-facio-block-dimension-escapes-every-charge-cutoff` proves that
every fixed size cutoff has charge zero.  Hence a surviving block model must
use a non-tight finitely additive charge concentrated at dimension infinity;
countably additive or tight mixtures of growing matrix fibers are excluded.

Nor must the common blocks be supplied beforehand.
`fournier-facio-generator-support-components-escape-cutoffs` forms
the support graph of charge-null comparison unitaries for one finite
generating set and proves that every bounded finite-component stratum has
charge zero.  Thus genuinely overlapping finite-band frames survive only if
their support graph has infinite components on positive charge, or if its
finite component sizes themselves escape to infinity in the finitely
additive charge.

Bare hyperfinite exhaustion does not eliminate the first survivor.
`fournier-facio-hyperfinite-support-exhaustion-misses-cutoff` gives an exact
singular amenable regular-character calibration whose support graph has one
infinite component and is exhausted by uniformly finite nested relations.
Each finite stage has boundary charge tending to zero but still strictly
positive.  Even promoting this to one fixed null-boundary finite-block
comparison would not suffice:
`fournier-facio-dimension-at-infinity-escape-is-sharp` constructs such a
comparison with every bounded block-size stratum of charge zero.  Closing
this face therefore requires a **tight** Cartanization theorem, a uniform
constraint on internal matrix dynamics as dimensions diverge, or a direct
obstruction on the genuinely infinite support component.

The first uniform internal constraint is now known.
`fournier-facio-fixed-block-spectrum-escapes` uses nonsoficity to find a
nontrivial group element fixing positive block charge and then uses
torsion-free power recurrence to prove that its number of distinct internal
eigenphases escapes every finite cutoff.  Thus dimension-at-infinity cannot
be supplied merely by amplifying a bounded spectral model.  A positive
common-block construction needs genuinely increasing spectral complexity on
the fixed sector.

The complete marginal law is also forced.
`fournier-facio-fixed-block-actor-is-charge-haar` shows that every nonzero
power moment of this fixed-block actor vanishes under the normalized charged
corner state.  Its aggregate spectrum is exactly Haar, not merely large or
dense, and each fixed power has vanishing diagonal coefficient columnwise in
charge.  Equivalently every fixed Krylov window
`delta_x,U delta_x,...,U^N delta_x` is asymptotically orthonormal on a
conull part of the fixed sector.  This excludes Haar-distributed irrational
diagonal phases as well as biased dense spectra.  The signed-square cyclic
splice shows that the Haar-and-wandering one-actor condition is attainable at
dimension infinity.
The remaining difficulty is therefore simultaneous: couple that off-diagonal
Haar field to the other generators and both compressors without reverting to
a monomial near action.
