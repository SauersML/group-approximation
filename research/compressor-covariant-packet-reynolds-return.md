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
  semisimple-packet-multiplicity-collapse: that seeks pointwise corona collapse for arbitrary finite-window semisimple packets at their self-normalized defect scale; this needs only the explicit Schur-Clifford packets on an extensive forbidden carrier supplied by the robust BCS gap.
  adjoint-supertrace-cannot-pay-hs-selection-load: that rules out paying a matrix carrier from one low-dimensional adjoint direction; this starts with a positive-density Reynolds range and must transport the whole projection rather than select one vector from it.
  schur-complement-controls-relative-pauli-module: that reduces the forbidden core of the Reynolds range to a three-generator module over the packet commutant; this must make those controlled coefficients covariant by genuine group relations without a finite-group selector soundness error.
---

Construct a finite group-relation gadget around a fixed Kazhdan group
`Lambda`, a one-sided compressor `s`, and the finitely many contextual packet
inclusions `A_(f_c)<=B_(f_c)` such that:

1. the gadget has an exact finite-tracial representation realizing the fixed
   non-CE BCS trace and a separated marked word;
2. in every finite-dimensional approximate representation, after local packet
   exactification, the adjoint Reynolds projections obey

   ```text
   sum_c tr_Adj(R_(A_c)-R_(B_c))
     <= C E_rel(U),                                      (CPR1)
   ```

   where `E_rel` is a bounded-overlap sum of named group-relator energies and
   `C` is dimension independent; and
3. at least one named covariance relator fails by a fixed amount in the
   tensor-decoupled representation of
   `packet-kazhdan-commutant-placement-decouples`.

The intended mechanism is to make the `R_A-R_B` range a genuine coefficient
of a compressor conjugacy orbit, so `scaled-kazhdan-transport` returns it to a
subspace of the same adjoint dimension.  Bare relations
`[A_f,Lambda]=[B_f,s Lambda s^(-1)]=1` are explicitly insufficient.

## Attempts

- **Bare commutant placement: refuted.**  The separate tensor-factor model
  retains the full Reynolds gap with zero transport defect.
- **Identify packet generators with fixed conjugates: too rigid.**  A fixed
  conjugate word cannot implement the selector-dependent Schur-complement
  retraction on all allowed assignments; doing so would revive the finite
  selector-induction barrier.
- **Active interface.**  Use a two-cell of rectangular intertwiners rather
  than equality of packet generators.  The cell should expose the whole
  Reynolds range as a transported adjoint coefficient, while the non-CE
  tracial model absorbs the corresponding infinite-index relative commutant.
- **Projective automorphism square.**
  `commuting-automorphism-cocycle-forces-multiplicity` gives an exact finite
  group-theoretic two-cell: a cocycle of order `r` forces `r` to divide the
  external packet multiplicity.  One fixed square still dilutes as `O(r/m)`;
  the covariance target would have to create positive-density independent
  squares or make the activated cocycle order exceed the current model size.
- **Canonical three-coefficient frame.**
  `schur-complement-controls-relative-pauli-module` removes arbitrary adjoint
  selection from the problem: three explicit controlled coefficients generate
  the entire `3 sum m^2` forbidden core as a module over the packet
  commutant.  The next relation may therefore be designed for those three
  coefficients rather than for an unknown Reynolds projection.
- **Finite groupification barrier.**  Those coefficients are additive
  central-Fourier combinations of packet words.
  `controlled-central-phase-finite-group-barrier` proves that adjoining their
  nonlinear commutator as a central element of a finite overgroup necessarily
  introduces wrong-phase selector irreducibles.  The covariance step must use
  the infinite compressor or a tracial corner; a larger finite packet cannot
  close it.
- **Adaptive cocycle-rank endpoint.**
  `projective-holonomy-rank-forces-exponential-multiplicity` computes the
  whole cancellation freedom: binary packet holonomy of rank `2r` moves to a
  Clifford action on the external multiplicity, forcing `2^r` to divide it.
  Hence a compressor construction closes this claim if it activates, with
  dimension-independent HS loss, cocycle rank strictly above the logarithm
  of the current packet multiplicity.  Fixed-rank holonomy cannot suffice.
- **Regular finite packets do not suppress the wrong sectors.**
  `regular-finite-controlled-phase-has-half-wrong-mass` shows that any
  nonaffine proposed phase has exactly one-half wrong mass in every regular
  selector sector.  The infinite compressor must perform genuine
  state-dependent selection; it cannot merely enforce regular type for a
  larger finite overgroup.
