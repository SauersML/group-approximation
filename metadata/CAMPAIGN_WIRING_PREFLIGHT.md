# Wiring pre-flight for the three-target campaign

Lane `audit-gate`, 2026-09-05.  Companion to `metadata/THREE_TARGETS_STATUS.md`.

Lanes are forbidden from editing the root, so every module this campaign has
produced is an orphan: nothing compiles it, no `#audit` line inside it ever
fires, and `scripts/check_import_regression.py` is red.  Wiring them is the
lead's job.  This file is the structural pre-flight for that job — what is
safe, in what order, and what can be done **without waiting for the vendored
Borsuk–Ulam port**.

Everything here is computed from the actual `import` lines, not from memory.

## The three structural checks, all currently clean

| check | result |
|---|---|
| import cycles, corpus-wide (4 320 project modules) | **none** |
| dangling project imports, corpus-wide | **none** |
| duplicate declarations, 25+ new modules vs 58 894 indexed qualified names | **none** |

The cycle check matters because a build probe cannot see a cycle: it is not a
compile error until the root pulls both ends in, at which point it takes main
down.  The dangling-import check matters for the same reason.  Neither is a
claim that anything compiles.

## The closure

Seeded at the 32 modules that are orphan now and were not orphan at baseline,
the orphan-only import closure is **222 modules**, and it topologically sorts
(no cycle).  Of those, **169 are `ThirdParty.HamSandwich.SphereOddDegree.*`**
— the vendored port, whose own layered order is already derived in
`fed6e4fa1` — and **53 are the campaign's own work**.

## The finding: 45 modules can be wired with no port dependency at all

Positions 1–45 of the topological order contain **no HamSandwich module**.
That batch can be wired and built today, independently of the two port lanes,
and it includes two things worth having now:

* **`GroupApproximation.Analysis.STW22ConditionalNegativeSolution` (position
  41).**  This is the operator-algebraic half of the XXII counterexample in its
  conditional form — `negativeSolutionToProblemXXII_of_borsukUlam` and the four
  theorems under it — and its only dependencies are
  `STW22AntipodalNormComparison` and `STW22AntipodalTraceSimplexBauer`, both in
  the same batch.  **It does not import the port.**  So the entire
  operator-algebra side of target 2 — the gauge identity, injectivity of
  `canonicalExtension`, its non-surjectivity given Borsuk–Ulam, the Bauer
  simplex, the compact metrizable boundary — can be *compiled and axiom-audited
  now*, with the topology left as the explicit hypothesis it already is.  That
  turns target 2 from "entirely unbuilt" into "one hypothesis away from built",
  and it does it without touching the 169-module port.
* **`GroupApproximation.Manuscript.NinetyNineProblems.ProblemXWitness`
  (position 45).**  Zero new dependencies — it imports only `ProblemX`, which
  is already in the root closure.  It is the cheapest wire in the batch and it
  carries the better public statement of the X(1) refutation
  (`exists_tracialState_isAmenableTrace_not_isQuasidiagonalTrace`: existential
  form, trace bundled so tracialness is part of the witness rather than an
  assumption about it).  Its three `#audit_closed_axioms` lines are inert until
  it is wired.

Recommended order, therefore: `ProblemXWitness` first (one import, lowest
risk, on the only target already green), then the STW22 chain up to
`STW22ConditionalNegativeSolution`, then the AlgTop/LIX algebra, and the port
last, in its own derived order.

## The batch, in dependency order

Positions 1–45.  A module is wireable once every line above it is.

```
 1. AlgTop.BundleCalculusProjection
 2. AlgTop.ChernNewtonSquareZero
 3. AlgTop.ChernParityAlgebra
 4. AlgTop.ChernParityCoefficient
 5. AlgTop.ChernSeries
 6. AlgTop.ChernEvenTopClass                     <- ChernSeries
 7. AlgTop.ChernSplitNewton                      <- ChernSeries, ChernNewtonSquareZero
 8. AlgTop.ChernSquareZeroIdeal
 9. AlgTop.ComplexProjectiveBasic
10. AlgTop.CPTautologicalSection                 <- ComplexProjectiveBasic
11. AlgTop.ComplexProjectiveChart                <- ComplexProjectiveBasic
12. AlgTop.ComplexProjectiveHyperplane           <- ComplexProjectiveChart
13. AlgTop.EulerLocalModel
14. AlgTop.MappingTorusSectionZeros
15. Analysis.CStarMatrixBlockInclusion
16. Analysis.CStarUnitaryComponent
17. Analysis.LIXFiniteStageNullHomotopy
18. Analysis.LIXObstructionComplementUnitary
19. Analysis.LIXObstructionSegment
20. Analysis.LIXProjectiveSpaceModel
21. Analysis.STW22AntipodalBlockTraceClassification
22. Analysis.STW22AntipodalBlockTraceMeasure     <- 21
23. Analysis.STW22AntipodalBaseCoordinateMeasures<- 22
24. Analysis.STW22AntipodalBaseBoundaryMeasure   <- 23
25. Analysis.STW22AntipodalBlockMeasureTrace     <- 22
26. Analysis.STW22AntipodalBlockTraceAffineEquiv <- 25
27. Analysis.STW22AntipodalBlockComplexCenter    <- 26
28. Analysis.STW22AntipodalBoundaryComponents    <- 24
29. Analysis.STW22AntipodalNormComparison
30. Analysis.STW22BauerSimplexImage
31. Analysis.SequentialGroupColimit
32. Analysis.TracialStateWeakStarTopology
33. Analysis.STW22AntipodalBoundaryTraceFunction <- 25, 32
34. Analysis.STW22AntipodalBoundaryMeasureTrace  <- 33, 24
35. Analysis.STW22AntipodalTraceMeasureInverse   <- 34, 26
36. Analysis.STW22AntipodalCoordinateRestriction <- 28, 27, 35
37. Analysis.STW22AntipodalFiniteBoundaryMeasure <- 36
38. Analysis.STW22AntipodalBoundaryMeasureRoundTrip <- 37
39. Analysis.STW22AntipodalTraceSimplexIntegration  <- 34
40. Analysis.STW22AntipodalTraceSimplexBauer     <- 39, 35, 38, 30
41. Analysis.STW22ConditionalNegativeSolution    <- 29, 40
42. KTheory.MatrixProjection
43. Analysis.LIXCornerAlgebra                    <- 20, 42
44. KTheory.BlockMoves                           <- 42
45. Manuscript.NinetyNineProblems.ProblemXWitness
```

## What still needs the port

Positions 46–222.  The port itself (169 modules), and then, in order:

```
 66. AlgTop.CochainLeibniz          <- SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap
 98. AlgTop.SingularCohomology      <- CochainLeibniz, SphereOddDegree.…SingularCohomologyHomotopyInvariance
 99. AlgTop.CupProduct              <- SingularCohomology
100. AlgTop.CupAssoc                <- CupProduct
219. Topology.TautologicalCommonZero
220. Topology.TautologicalAntipodal <- TautologicalCommonZero
221. Topology.OddMapNormalization   <- TautologicalAntipodal
222. Topology.AntipodalObstructionFromOddDegree
        <- OddMapNormalization, SphereOddDegree.ComplexOddMapCommonZero
```

`Analysis.STW22NegativeSolution` — the unconditional XXII endpoint — sits above
222, since it applies the conditional form to
`complexOddMapCommonZero_unconditional` and so pulls the port in.  That is the
right dependency: it is the module whose whole content is *"the hypothesis is
discharged"*.

## Standing caveats

* None of this says anything compiles.  A clean graph, a clean name index and a
  clean lexical scan are three ways a module can fail to be broken; they are
  not a build.
* `#audit` macros read **oleans**.  When a module is wired and built, the
  audit line inside it reports on whatever the build produced — so if the job
  count does not move on a real change, the probe replayed and the report is
  about old code.
* Wiring a module elaborates it **for the first time**.  Expect the first build
  after each batch to be where the errors are, not the second.
