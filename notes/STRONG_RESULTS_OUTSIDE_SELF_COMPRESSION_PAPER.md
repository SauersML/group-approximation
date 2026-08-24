# Strong results intentionally kept outside the self-compression paper

Date: 2026-08-24

This note records the strongest established results removed from the manuscript
`non_mf_groups_exist.tex`.  They remain mathematically valuable, but they use a
different analytic architecture from the exact finite-dimensional
self-compression theorem and are not part of the current paper.

Nothing listed here should be reintroduced merely as an additional consequence.
Each item belongs in a later paper only if it helps define that paper's single
thesis.

## Exact approximation loss for compression wreath products

For the affine-doubling compression pair and every finite lamp group `K`, the
canonical quotient

```text
W_K -> K_ab^(Z) semidirect G_*
```

computes the full information retained by norm-matrix-corona representations.
Its kernel is simultaneously the MF, finite-dimensional unitary,
finite-dimensional linear, Bohr, and finite residual.  The strongest form is
the universal Hom-set factorization theorem, not the list of five radicals.

High-impact consequences include:

- a sofic group which is not MF;
- a single MF-invisible involution whose normal closure is the exact MF radical;
- a relation already satisfied by every MF representation whose imposition
  changes the MF property;
- profinite twins with opposite MF behaviour.

Primary pointers:

- `research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md`
- `research/compression-wreath-five-radicals-coincide.md`
- `research/simple-lamp-radical-one-relation.md`
- `GroupApproximation/Algebra/VisibleQuotient.lean`
- `GroupApproximation/Sofic/LinearResidual.lean`
- `GroupApproximation/Algebra/FiniteResidual.lean`

## Spectral rigidity and the sharp abelian boundary

One-sided Kazhdan compression fixes clopen spectral data for a normal corona
element with commuting conjugates.  Equivalently, conjugation can move the
element only within connected components of its spectrum.  The slow-wall
construction supplies the opposite direction and yields the exact abelian
classification

```text
A^(X) semidirect G_* is MF  <=>  A is torsion-free.
```

This is the strongest mechanism-and-boundary package removed from the paper.
It should remain together if developed elsewhere: the negative spectral
theorem without the positive slow-wall theorem is incomplete conceptually.

Primary pointers:

- `notes/COMPRESSION_COLLAPSE_MF_RADICAL.md`
- `research/path-map-lamp-mf.md`
- `GroupApproximation/Analysis/SpectralComponentMotion.lean`
- `GroupApproximation/Sofic/SpectralCompression.lean`
- `GroupApproximation/Manuscript/SpectralPaper/MainTheorems.lean`

## Finite noncommutative packets

The finite-packet theorem removes the commuting-orbit hypothesis by using
finite-dimensional exactification and multiplicity rigidity.  The concrete
`S_9` star packet shows that one-sided compression can collapse a centerless
finite packet whose conjugates do not commute.

This result is not a clean substitute for the spectral paper: its proof still
uses rank-normalized Hilbert--Schmidt geometry and scaled Kazhdan transport.

Primary pointers:

- `notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md`
- `research/arithmetic-star-packet-non-mf.md`
- `research/finite-packet-covariance-polar-correction.md`

## Total MF invisibility

Two established constructions reach the stronger endpoint

```text
Rad_MF(Q) = Q.
```

The Hilbert-hotel/Leavitt construction saturates one algebraic compression
defect until it normally generates the entire group.  The separate
small-cancellation compiler routes one weak shadow defect into a finitely
presented torsion-free Kazhdan group with full MF radical.  These are stronger
endpoints than a single non-MF witness, but their present proofs use analytic
or group-theoretic machinery intentionally excluded from the current paper.

Primary pointers:

- `research/hilbert-hotel-model-is-unconditionally-non-mf.md`
- `research/hilbert-hotel-block-cover-is-unconditional.md`
- `research/artifacts/hilbert-hotel-st20-full-mf-radical-2026-08-21.md`
- `research/defect-saturation-full-mf-radical.md`
- `notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md`

## Computability consequences

The fixed MF-radical computer and its incompleteness refinements show that
membership in MF radicals can encode halting and proof-theoretic information.
These results are high impact but belong to a paper about the logical
complexity of approximation radicals, not a paper about self-compression in
finite dimension.

Primary pointers:

- `research/reverse-kleene-support-profile-nonmf.md`
- Cairn nodes for the MF-radical computer and Gödel-word refinements

## Editorial boundary

The current manuscript retains only:

- exact finite-dimensional commutant rigidity over every field;
- the binary Leavitt self-compression;
- one explicit defect normally generating the whole elementary group;
- triviality of all finite-dimensional, compact, and residually finite images.

The results above remain in Cairn and in their source artifacts.  They are
excluded from the manuscript to prevent several distinct proof architectures
from being presented as one theory.
