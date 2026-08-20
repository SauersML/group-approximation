---
rg: 2
id: compressor-covariant-packet-reynolds-return
kind: claim
title: Couple packet Reynolds ranges to a one-sided compressor with dimension-free return cost
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  scaled-kazhdan-transport: that transports matrices already known to asymptotically commute with a Kazhdan image; this must make the explicit packet Reynolds-difference range enter that transported sector by group relations.
  packet-kazhdan-commutant-placement-decouples: that gives the tensor-factor countermodel to bare commutant placement; this asks for a covariance relation which excludes exactly that model.
  adjoint-supertrace-cannot-pay-hs-selection-load: that rules out paying a matrix carrier from one low-dimensional adjoint direction; this starts with a positive-density Reynolds range and must transport the whole projection rather than select one vector from it.
  schur-complement-controls-relative-pauli-module: that reduces the forbidden core of the Reynolds range to a three-generator module over the packet commutant; this must make those controlled coefficients covariant by genuine group relations without a finite-group selector soundness error.
  support-packet-literal-tensor-covariance-is-blind: that rules out replacing Reynolds-range covariance by literal equivalence of two tensor representations, even with arbitrary virtual coefficients; this must transport the commutant functor itself.
---

Construct a finite group-relation gadget around a fixed Kazhdan group
`Lambda`, a one-sided compressor `s`, and the contextual packet inclusions such
that it has the required exact non-CE tracial model and, in every
finite-dimensional approximate representation, local packet exactification
gives canonical forbidden-core projections
`K_c<=R_(A_c)-R_(B_c)`.  Their density is bounded below by a fixed constant
times the square of the forbidden packet mass, and

```text
sum_c tr_Adj(K_c) <= C E_rel(U).                      (CPR1)
```

Controlling the whole Reynolds difference is sufficient but is not required.
Here `E_rel` is a bounded-overlap sum of named relator energies and `C` is
dimension independent.  At least one named covariance relator must fail in
the tensor-decoupled model of
`packet-kazhdan-commutant-placement-decouples`.

## Attempts

- Bare commutant placement is refuted by the tensor-factor model.
- Identifying packet generators with fixed conjugates is too rigid: one fixed
  word cannot implement the selector-dependent Schur-complement retraction.
- A two-cell of rectangular intertwiners may expose the whole Reynolds range
  as a transported coefficient while the exact non-CE model absorbs the
  infinite-index relative commutant.
- `commuting-automorphism-cocycle-forces-multiplicity` supplies an exact
  projective two-cell, but a fixed cocycle order only gives a dilutable
  divisibility condition.
- `schur-complement-controls-relative-pauli-module` removes arbitrary adjoint
  selection from the problem: three explicit controlled coefficients generate
  the entire `3 sum m^2` forbidden core as a module over the packet
  commutant.  The next relation may therefore be designed for those three
  coefficients rather than for an unknown Reynolds projection.
- Those coefficients are additive central-Fourier combinations of packet
  words.  `controlled-central-phase-finite-group-barrier`
  proves that adjoining their nonlinear commutator as a central element of a
  finite overgroup necessarily introduces wrong-phase selector irreducibles.
  The covariance step must use the infinite compressor or a tracial corner;
  a larger finite packet cannot close it.
- `projective-holonomy-rank-forces-exponential-multiplicity` computes the
  whole cancellation freedom: binary packet holonomy of rank `2r` moves to a
  Clifford action on the external multiplicity, forcing `2^r` to divide it.
  Hence a compressor construction closes this claim if it activates, with
  dimension-independent HS loss, cocycle rank strictly above the logarithm
  of the current packet multiplicity.  Fixed-rank holonomy cannot suffice.
- Finite regular normalization does not rescue controlled groupification.
  `regular-finite-controlled-phase-has-half-wrong-mass` shows that any
  nonaffine proposed phase has exactly one-half wrong mass in every regular
  selector sector.  The infinite compressor must perform genuine
  state-dependent selection; it cannot merely enforce regular type for a
  larger finite overgroup.
- `schur-packet-child-square-is-pauli-transverse` supplies a way around the
  additive controlled-phase wall: factor the rank gate through the two actual
  finite children `B_f^P` and `B_f^Q`.  Their centered commutant modules are
  the transverse `Z` and `X` Pauli directions exactly on forbidden sectors.
  The live route `covariant-return-via-schur-child-masas` reduces this claim
  to returning those two genuine child modules through one infinite
  compressor cell.
- `support-packet-covariant-wedderburn-detector` gives an exactly
  automorphism-covariant coefficient whose commutants are allowed-flat and
  separated by `1/49` on the forbidden simple.  The tempting stronger HNN
  relation on the tensor representations cannot implement it:
  `support-packet-literal-tensor-covariance-is-blind` proves that every
  virtual coefficient difference killed by all allowed tensor functors is
  also killed by the forbidden tensor functor.  Thus the stable letter must
  normalize a canonically exposed Reynolds range (or a finite unitary frame
  spanning it), not conjugate the two diagonal packet representations.
- A finite-Heisenberg coefficient exactifier would remove arbitrary
  coefficient multiplicity only if its marked spin algebra canonically
  exposes that Reynolds frame.  Merely placing the coefficient in a unique
  Stone--von Neumann block is insufficient for a literal HNN, by the preceding
  annihilator theorem.  This is now a precise design constraint rather than an
  open-ended multiplicity-reservoir warning.
- The Reynolds range now has a fixed word frame.
  `support-packet-paired-word-frame-exposes-forbidden-rank` constructs four
  paired packet words spanning the changing `M_2^4/C^16` summand.  Their two
  symbolic class-two groups are isomorphic, but all 32 edge isomorphisms send
  forbidden source character `101` to reverse character `011`.  The remaining
  compressor relation only has to prevent that one reverse reservoir from
  returning; it no longer has to select an unknown adjoint projection or an
  arbitrary multiplicity basis.
- Conditional dilution is no longer an analytic loophole.
  `corner-localized-non-ce-bcs-energy-gap` gives a soundness floor proportional
  to the trace of every approximately reducing transported carrier, and
  `first-hit-carrier-contraction-ladder` converts persistent baseline copies
  plus orthogonal `011` exits into the required linear reservoir bound.  The
  remaining issue is therefore literal word-level persistence and
  orthogonality, not a new compactness or corner-normalization theorem.
