# Named open-problem attack log

This file records the problems from the researcher list that were actively
checked against the current Cairn/Lean repository.  “Not solved” means no
valid route was found; it is intentionally not euphemized as a conjectural
solution.

## 1. Alon Dogon — Iwahori matching / Question 1.4

**Status: NOT SOLVED.**

Cairn has a very sharp live reduction:

`edge-pair-mixed-gap-collapse`
  -> `iwahori-outlier-localization`
  -> `iwahori-outlier-repair`
  -> `iwahori-sector-closure`
  -> `non-hyperlinear-group`.

The repository already proves that in the central-regular regime the mixed
edge representation has regular spectral bulk and only an `o(d_n^2)`
low-energy outlier; the identity matrix is asymptotically contained in that
outlier.  It also proves index-three restriction/induction has uniformly
bounded branching.

The remaining obstruction is genuinely physical-rank rather than
Hilbert-space dimension.  An `o(d_n^2)` operator subspace can contain a
full-rank invertible matrix (the scalar line is the basic example), and
bounded branching does not prevent the identity's mass from spreading over a
growing number of cross-pairs of edge constituents.  I found no valid
argument turning the sparse low-energy outlier into `o(d_n)` removable
padding, nor a uniform transversality theorem for the two opposite modular
extension loci.

Useful files (the derivation chain is reproducible via
`cairn why non-hyperlinear-group`):

- `docs/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md`
- `docs/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`
- `docs/TRUE_IWAHORI_MIXED_GAP_DICHOTOMY.md`
- `docs/TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md`
- `docs/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md`

## 2. Alex Lubotzky — flexible operator-norm stability of Z^3

**Status: NOT SOLVED.**

The repo has operator-norm corona/stability machinery, Bott/K-theoretic
obstruction infrastructure, and a large amount of exact finite-matrix
technology, but it does not currently contain a dedicated Cairn reduction of
the Lubotzky--Salomon `Z^3` question.  The existing machinery is insufficient
to infer a flexible lift for triples of almost-commuting unitaries.  In
particular, the `Z^2` flexible theorem cannot simply be iterated while
preserving the third commutator.

A responsible next project would first encode the stabilization-dimension
invariant and distinguish:

1. finite stabilization dimension;
2. a linear stabilization bound;
3. full flexible stability.

No one of these is established here.

## 3. Francesco Fournier-Facio — Frobenius stability of SL_3(Z)

**Status: NOT SOLVED.**

The repo contains Frobenius/rank estimates and substantial property-(T)
machinery, but it does not have the full `(T_2)`/degree-two cohomological
formalism needed to turn those estimates into a proof of Frobenius stability
for `SL_3(Z)`.

Do not confuse this with the **new solved result in this bundle**:
`fournier-facio-group-matricially-stable` concerns Fournier-Facio's 2026
*torsion-free nonsofic group* and operator-norm matricial stability.  It is a
different group, norm, and question.

## 4. Fournier-Facio / Rufus Willett — pentagon RAAG LLP/RFD

**Status: NOT SOLVED.**

`GroupApproximation/Algebra/GraphProduct.lean` is useful algebraic
infrastructure, but LLP is a lifting/tensor-product property of full group
C*-algebras.  The current library does not contain enough LLP technology to
turn the graph-product formalization into Question 1.7.  No valid shortcut
through MF/RFD was found.

## 5. Rufus Willett — free-by-cyclic conditional stability

**Status: NOT SOLVED.**

The repo can express HNN/semidirect-product structure and operator-norm almost
representations.  It does not presently supply the KK/eta obstruction
machinery in Willett's proof, nor an elementary replacement.  No route from
the existing transport lemmas to conditional stability was found.

## 6. Caleb Eckhardt — dense periodic measures / HS stability

**Status: NOT SOLVED.**

The repo has semidirect-product and HS approximation technology but almost no
Pontryagin-dual/topological-dynamical infrastructure.  The missing statement
is not just a matrix estimate; it is density of periodic invariant measures
for a class of algebraic dynamical systems.  No existing Cairn theorem
collapses that step.

## 7. Tatiana Shulman — hyperlinear trace versus MF trace

**Status: ALREADY SOLVED IN THE INPUT REPOSITORY; NOT COUNTED AS NEW.**

See `cairn why hyperlinear-trace-not-mf-trace` and
`GroupApproximation/Sofic/TraceSeparationEndpoint.lean`.

## 8. Dadarlat, Gorfine/Glasner, Scott Sauers

No additional current named problem attached to these entries was closed in
this pass.  I did not manufacture a “solution” from thematic proximity.
