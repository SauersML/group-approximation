---
rg: 2
id: hs-finite-adaptive-ring-tree-decoder
kind: claim
title: Decode the finitely many conditional partial-isometry corners of the adaptive BCS tree
distinct_from:
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That embeds the entire conditional coefficient quotient into a rank-metric ultraproduct; this asks only for the fixed finite corner and product table used by one bounded tree.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: That recovers a full relative Leavitt cell on one root carrier; this recovers finitely many selected source/range pairs and their carrier joins.
  finite-adaptive-selected-atom-ring-tree: That is the exact coefficient-ring compiler; this is its missing normalized-HS group-microstate interpretation.
---

**OPEN FINITE METRIC DECODER.**  Apply rank-five Steinberg wordization to
the coefficient presentation of `finite-adaptive-selected-atom-ring-tree`.
For every canonical normalized-HS microstate with the central mark
separated, recover projections and contractions on the prescribed spectral
carrier of the seed root so that, simultaneously for the finitely many
nodes,

```text
||Sbar_(sigma,i)S_(sigma,i)-A_(sigma,i)||_2=o(1),
||S_(sigma,i)Sbar_(sigma,i)-D_(sigma,i)||_2=o(1),
||D_(sigma,i)Q_sigma||_2=o(1),                         (HAT1)
||D_(sigma,i)(1-Q_-)||_2=o(1),
```

and the decoded `Q_(sigma i)` reduces the next shared BCS window.
The error modulus may depend on the fixed BCS and depth `N`, but not on the
matrix dimension.

No faithful model of the whole coefficient ring is requested.  Only the
finite multiplication table in `(HAT1)`, on the root spectral carrier fixed
before choosing coefficient operators, is needed.  Nevertheless scalar
finite-window multiplicity data are insufficient: the source and range
products have to be realized on one physical carrier.  Full-rank
small-singular-value defects also prohibit a direct HS-to-rank-kernel cut.

`murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness` removes one
apparent part of `(HAT1)`: each source and range root packet is already
exactly conjugate in every abstract group representation.  The irreducible
residue is **orthogonal-sum localization**.  The decoder must show that the
packets named by `Q_sigma`, `D_(sigma,i)`, and
`Q_(sigma i)=Q_sigma+D_(sigma,i)` occupy one common matrix reservoir, so
their decoded traces add.  Separate typed carriers, even with exactly equal
source/range spectral data, do not suffice.

For the terminal contradiction, actual corner operators are stronger than
necessary.  `hs-steinberg-morita-trace-additivity-on-adaptive-blocks`
isolates the scalar remnant: the fixed conjugacy witnesses already prove all
algebraic equivalences, and only additivity of physical mass across a
stabilized diagonal block remains.

Establishing `(HAT1)` yields `(FAT1)` with `eta=1-o(1)` along every reached
branch.  Conversely, the exact perfect BCS model has all `A_(sigma,i)=0`, so
the decoder is allowed to return zero arrows there and creates no universal
tracial contradiction.

## Attempts

- **Exactify each finite root/Heisenberg window.**  This recovers the scalar
  source and range multiplicities, but the corrections at different tree
  edges need not select the same physical corner.  The products in `(HAT1)`
  are precisely the missing alignment data.
- **Cut off small singular values of every relator defect.**  HS-small
  matrices may have full rank, so the intersection of the resulting
  approximate kernels can have zero density even at fixed tree depth.
- **Replace the decoded ranges by an independent finite address packet.**
  `independent-address-capacity-cannot-drive-selected-atom-growth` shows
  that this conserves exactly the trace one is trying to amplify.  The
  decoder has to retain the conditional payload product, not just its rank.
- **Use only the finite parent/child root subgroups.**  Once a selected
  coefficient corner is physically located, their restriction mismatch is
  paid by `finite-group-multiplicity-mismatch-pays-hs-energy`.  But fixed
  root-window density measures do not locate that corner:
  `orthogonal-steinberg-root-spectral-support-is-not-additive` shows that
  orthogonal coefficient idempotents and their sum can have the same root
  support.  Thus the finite-group shortcut solves the terminal payment, not
  the prescribed-carrier additivity in `(HAT1)`.
