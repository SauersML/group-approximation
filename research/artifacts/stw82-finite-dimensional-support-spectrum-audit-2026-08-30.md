---
rg: 2
title: STW LXXXII finite-dimensional support-spectrum colouring audit (2026-08-30)
kind: artifact
---

# Imported topological input

The only imported theorem is Ostrand's coloured characterization of
covering dimension.  In the form used here, every open cover of a metrizable
space of covering dimension at most `n` has an open refinement which is the
union of `n+1` discrete families.  For the compact spectrum and finite local
cover in this argument, the refinement may be taken finite.

This is the metric-space theorem of Phillip A. Ostrand, *Dimension of metric
spaces and Hilbert's problem 13*, Bulletin of the American Mathematical
Society 71 (1965), 619--622,
[DOI 10.1090/S0002-9904-1965-11363-5](https://doi.org/10.1090/S0002-9904-1965-11363-5).
Ostrand's later general-space treatment is *Covering dimension in general
spaces*, General Topology and its Applications 1 (1971), 209--221,
[DOI 10.1016/0016-660X(71)90093-6](https://doi.org/10.1016/0016-660X(71)90093-6).

A finite partition of unity subordinate to the refinement is chosen with
each function's closed support contained in its assigned open set.  This is
the standard finite normal-space partition-of-unity construction; compact
metrizability is more than sufficient.

# Why cover order alone is insufficient

An open refinement of multiplicity at most `n+1` is not enough for the
operator argument.  Its intersection graph need not be `(n+1)`-colourable.
Ostrand's discrete-family refinement supplies an actual colour on every
refinement set.  Within one family, the subordinate functions have disjoint
supports, so cutters carrying the same topological colour annihilate
exactly.  This is the step which converts covering dimension into order-zero
colour capacity without an unproved graph-colouring assertion.

# Coupled selection and error ledger

At a point `x`, at most `m` outgoing supports are nonzero.  A neighbourhood
of `x` makes every other support smaller than the target error.  Each
Ostrand refinement set inherits such an active set and injects it into `m`
support labels.  Pairing the `n+1` topological family labels with the `m`
active-support labels gives `(n+1)m` cutters.

The partition of unity sums to one.  Consequently all omitted terms sum to
at most `epsilon`, not to the number of cover sets times `epsilon`.  The
cutters lie in the common relative commutant, so their cutdowns are already
exact order-zero maps; no cone-projectivity perturbation is required.

# Exact boundary

The result is an outgoing-family replacement theorem.  It does not assert
that an arbitrary reduced stable essential extension has finite-dimensional
central support spectrum, nor that the product bound is optimal for
positive-dimensional spectra.  It does prove the following precise
extension strategy: if endpoint approximations can be placed in a common
compact metrizable support algebra of dimension `n` and pointwise active
multiplicity `m`, their outgoing maps cost at most `(n+1)m` global colours.

The common-relative-commutant assumption is essential to this proof.  It
makes multiplication by a partition function preserve order zero.  Merely
placing the supports in a common commutative algebra does not imply that its
partition functions commute with the supporting homomorphisms.
