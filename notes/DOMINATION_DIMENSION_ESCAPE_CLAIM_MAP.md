# Quantitative radicals and dimension escape: claim map

Date: 2026-08-11

This file fixes the credit boundary and the current Lean status for the
paper-shaped development in `GroupApproximation/Domination/`.

| Claim or input | Credit | Lean status |
|---|---|---|
| Cartesian powers of finite actions | Standard sofic-approximation amplification | Proved in `Permutation.lean` |
| Tensor powers and conjugate doubling | Standard finite-dimensional representation theory | Proved in `Unitary.lean` |
| Sofic groups embed in hyperlinear groups by permutation matrices | Elek--Szabó | Exact defect comparison proved in `Comparison.lean` |
| Qualitative collapse iff one linear domination inequality | Paper-specific presentation-dependent linearization | Proved abstractly and instantiated on both sides |
| `C_perm ≤ C_fd` in predicate form | Standard permutation-matrix inclusion; paper-specific scalar packaging | Proved in `Comparison.lean` |
| Exact finite-action radical test | Presented-group universal property + finite groups are sofic | Proved in `PresentationRadical.lean` |
| Fixed-dimension domination from a sofic-radical word | Paper-specific target theorem | Analytic curve-selection/jet bridge not yet proved |
| Semialgebraic curve selection | Classical real algebraic geometry | Not yet formalized; will be isolated |
| Truncation at the first surviving jet | Classical local-algebra technique | Residually-finite detector endpoint proved; jet construction remains |
| Finitely generated complex linear groups are residually finite | Mal'cev | Explicit typeclass boundary in `JetDetector.lean`; not claimed as ours |
| Affinity of normalized trace under direct sums | Standard character theory | Numerical weighted-block theorem proved in `Affine.lean` |
| Complete reducibility of finite-dimensional unitary representations | Classical unitary representation theory | Irreducibility API connected; construction of decompositions remains |
| Bounded irreducible degree is harmless | Paper-specific domination consequence of fixed-degree bounds | Proved for supplied irreducible decompositions |
| Any remaining obstruction needs irreducible degree tending to infinity | Paper-specific synthesis | Proved from fixed-degree bounds and failure of global irreducible domination |

The paper-facing API deliberately does not state the unfinished
curve-selection bridge as a theorem. The current headline endpoint
`obstruction_requires_irreducibleDegreeEscape` exposes its fixed-dimensional
input as a hypothesis until that input is formally discharged.

