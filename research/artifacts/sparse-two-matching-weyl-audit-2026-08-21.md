# Sparse two-matching Weyl audit — 2026-08-21

## Outcome

The exact mixed-incidence problem is closed much more strongly than the
original linear-mislabel calculation suggested.  For
`F=F_(2^n)` and a primitive `alpha`, the two matchings

```text
a=b,                       a=alpha b
```

force the complete cross-commutation table for arbitrary exact additive
actions in an arbitrary group after tensor untwisting.  In the twisted Weyl
form, every finite-dimensional exact model therefore has dimension divisible
by `2^n`.  Nonlinear character actions and arbitrary spectral multiplicities
are not exact escapes.

This is recorded in:

- `two-untwisted-field-matchings-force-complete-cross-commutation`;
- `two-field-centralizer-fiber-closure-proof`;
- `two-matchings-force-exponential-dimension-with-multiplicity`.

An independent Fourier-block proof was also obtained in
`two-matching-matrix-bridge-orbit-proof`; it gave the weaker but still
exponential lower bound `2^n-1` before the abstract centralizer-fiber theorem
superseded it.

## Quantitative frontier

The direct ratio-circuit robustification costs

```text
K_n <= 8 n 3^(ceil(log_2 n)),
```

so it does not supply the fixed normalized-HS threshold needed by the group
compiler.  Following one primitive affine orbit is worse: it telescopes over
`2^n-1` steps.  Thresholding individual Fourier blocks is invalid because
their masses can be arbitrarily small.

The useful analytic replacement is a spectral, not merely dimensional,
expander ledger.  If sparse mixed tests can be converted into transport of
one common marked PVM `(P_v)` over an exponentially large uniform-gap label
graph, then the scalar Poincare estimate

```text
E_PVM >= 2 gamma mu (1-d/|Omega|)
```

forces either `d>=|Omega|/2` or collapse of the marked mass `mu`.  This
dimension-free endpoint is proved in
`expander-pvm-transport-forces-dimension-or-mass-collapse`.

The remaining mixed analytic statement is exactly
`sampled-weyl-defect-controls-common-pvm-dirichlet-energy`: make the sampled
commutator defect control the summed transport energy of that one PVM.  A
dimension-expander hypothesis on coefficient subspaces alone is insufficient;
the proof needs a uniform Poincare/spectral gap for the induced label action.

## Same-basis interface

Before the mixed estimate, the occurrence game must round each basis to one
exact additive action, on the same Hilbert space and without context-dependent
PVMs or flexible dimension enlargement.  The minimal open input is recorded
as `same-basis-rounding-interface-for-sparse-weyl-sampler`.

Dense BLR has the right analytic flavor but its complete additive-triple
incidence is not a bounded-template small-cancellation object.  Equality-cloud
degree reduction recreates the known two-pair contour.  Thus the remaining
compiler has two clean and nonduplicative gates:

1. bounded-template same-basis rounding to one PVM;
2. mixed sampled-defect control of that PVM's expander Dirichlet energy.

The supplied Gowers--Hatami source was also audited at the same-basis
interface.  Its flexible partial representation can be repaired, for finite
abelian groups, to an exact representation in the original matrix dimension:
average the excess-space projection into the commutant, round to an invariant
projection of the required rank, and rotate by principal angles.  This gives
an `O(sqrt(epsilon))` universal modulus and is recorded in
`finite-abelian-hs-almost-actions-round-in-the-same-dimension`.  Therefore the
remaining same-basis problem is incidence-theoretic (bounded-template
all-pairs decoding), not finite-abelian HS stability.

No non-hyperlinear group proof is claimed by this audit.

## Subsequent simplification: the mixed table can be deleted

The strongest result of the lane is now
`one-pauli-seed-character-expansion`.  After one additive X action is
available, a single D8 anticommutation seed puts half of a surviving marked
carrier into nonzero X characters.  Bounded actor covariance whose dual
Schreier graph has gap `gamma` then gives

```text
d >= (2^n-1)/2
```

or

```text
marked mass <= 4 eta_act^2/gamma + eta_seed^2/4.
```

This removes the second additive table and every mixed X/Z rectangle.  The
remaining finite-family compiler needs only one same-basis additive table,
bounded actor covariance, and one D8 edge.

There is also a one-scale version:
`one-seed-infinite-character-expansion-collapses-mark`.  If a fixed actor has
a positive bottom spectral gap on one infinite nontrivial character orbit,
the finite-dimensional spectral rank vector has finite support and the
counting-measure Poincare inequality collapses it outright.  The unresolved
word-level interface is global same-basis decoding plus control of the full
character-orbit Dirichlet energy.  Cairn metadata was corrected so this
groupification gate remains explicitly OPEN.
