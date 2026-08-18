---
rg: 2
id: coherent-configuration-orbital-rounding
kind: claim
title: Near-normal characters give orbital algebras with almost integral structure constants
distinct_from:
  traffic-branching-rounding-hierarchy: that works with graph-indexed observables of the table itself and its target is a moment law; this works in the pair-space commutant and its target is an algebra with a nonnegative integral basis. The first is a moment problem, the second a rigidity-of-structure-constants problem.
  hyperlinear-implies-sofic: that is the group statement; this is a statement about the commutant of one finite-dimensional representation, and it aims at a finite relational structure — a coherent configuration — which is weaker than a permutation action and is a legitimate intermediate object in its own right.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**The structural asymmetry this exploits.**  When a finite group acts on a
finite set `X`, its commutant in `End(C^X)` has a canonical basis: the orbitals
of the action on `X × X`.  Those matrices `A_0,…,A_r` are `0/1`, their supports
partition `X × X`, transposition permutes them, the all-ones matrix is their
sum, and — the decisive property — each product `A_i A_j` is a **nonnegative
integer** combination of the `A_k`.  This is coherent-configuration /
association-scheme structure.  A general finite-dimensional unitary
representation has a semisimple C*-commutant with no reason to carry a
distinguished nonnegative integral basis at all.  So integrality of orbital
structure constants is a finite, checkable trace of being a permutation
representation.

**Target.**  Let `pi_n` be finite-dimensional representations of a free group
whose normalized characters converge to a normal `0/1` character `1_N`.  Then,
after balanced tensor amplification, the pair-space commutants admit finite
families of positive contractions `A_{n,0},…,A_{n,r_n}` that are approximately
orthogonal in the HS inner product, partition the relational mass, are
compatible with the generator action, and have structure constants within
`o(1)` of nonnegative integers.  Once those errors are below `1/2` under a
suitable normalization and rank control, the constants round *exactly*, and
what is left is a genuine finite coherent configuration.

**Why balanced amplification belongs here.**  For a representation `pi` the
pair space carries `pi ⊗ conj(pi)`; for a permutation representation on `C^X`
that is literally the action on ordered pairs `X × X`.  So the balanced
doubling of `balanced-replica-hs-amplification` — introduced there for phase
control — is the same operation as passing from points to pair orbitals on the
classical side.  The two programmes share their first step for a structural
reason, not by coincidence.

**Why this is not the Cartan/masa route.**  A masa route looks for a basis of
the original Hilbert space in which every `U_g` is almost monomial, and dies
on phase cancellation and on the failure of a common Cartan.  This route works
in the commutant, is basis-free at its first stage, and asks for integrality of
multiplication constants rather than for simultaneous diagonalization.

**Known obstruction, and why it is not fatal.**  Not every coherent
configuration is schurian — arises from a permutation group
(Hirasaka–Kim–Ponomarenko, arXiv:1801.01328).  So rounding to an exact
configuration does not automatically produce an action.  But a coherent
configuration *is* a finite relational model, and the remaining step becomes a
studied algebraic-combinatorial realization question rather than an arbitrary
operator problem; the route consuming this claim inherits that gap and says so.

## Attempts

- **Diagonalize the commutant and read off a basis.**  Produces the spectral
  projections, which are the wrong basis: they are orthogonal but have no
  reason to be `0/1`-like, and their products have arbitrary real structure
  constants.  Integrality is a property of the orbital basis, and nothing
  selects that basis spectrally.
- **Use the character convergence directly.**  It controls the trace of each
  generator's image, hence the diagonal of the pair-space data, but the
  structure constants are off-diagonal quantities; the missing input is a rank
  or multiplicity constraint that forces the off-diagonal mass to concentrate
  on few basis elements.  This is the technical heart and is open.
- **Deferred experiment:** for explicit small unitary tables with selected
  relators of trace near one, compute the pair-space commutant numerically,
  search for a positive approximately disjoint basis, and measure how close the
  multiplication coefficients can be driven to nonnegative integers.  If
  near-normal characters do not force integerization even numerically, this
  claim is dead and the intermediate category is the wrong one.
