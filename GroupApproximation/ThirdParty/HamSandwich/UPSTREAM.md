# HamSandwich vendoring record

This directory contains a namespace-isolated Lean 4.32 port of the smallest
transitive source slice needed for the Borsuk--Ulam endpoint from
[`akopjan/HamSandwich`](https://github.com/akopjan/HamSandwich).

- Upstream commit: `76202dbbb6610ffcebbccfbf7a56f833a4c2a376`
- Upstream Lean/mathlib: `v4.28.0`, mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Local target: Lean/mathlib `v4.32.0`
- Upstream license: Apache License 2.0
- Local namespace: `GroupApproximation.ThirdParty.HamSandwich`

The repository root [`LICENSE`](../../../../LICENSE) contains the same Apache
License 2.0 text. Porting changes are recorded in each source file. No theorem
is weakened and no placeholder or additional axiom is permitted in this tree.

## Audited dependency inventory

The upstream static import closure of
`HamSandwich.SphereOddDegree.BorsukUlam` contains 175 project modules, 31,437
lines, and 1,543,822 bytes at the pinned commit. A comment/string-aware scan of
that exact closure found no active occurrence of `sorry`, `admit`, `axiom`,
`constant`, `opaque`, `unsafe`, `implemented_by`, or `extern`.

The upstream kernel audit reports:

```text
'SphereOddDegree.borsuk_ulam' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## Port status

The first v4.32 incompatibility layer is being ported before importing the
remaining closure. The following modules are green on v4.32:

- `RPnCohomologyRingModel`: its model type is now an `abbrev`, allowing v4.32
  to reuse the quotient ring's canonical instances.
- `AffineBarycentricSubdivision`: its final dependent barycenter rewrite is an
  explicit equality calculation compatible with v4.32.
- `HomotopyToChainHomotopy`: its conclusion is changed directly to the
  `homologyMap` expression before applying the chain-homotopy theorem, avoiding
  a v4.32 functor-whiskering definitional-equality mismatch.
- `Basic`, `Antipodal`, and `RealProjectiveSpace`: namespace-only ports.
- `Covering`: replaces brittle `fin_cases` reductions of the order-two deck
  action by an explicit zero/nonzero split and the already-proved `proj_neg`.
- `AffineLastFaceIdentity`: replaces proof-term generalization and a dependent
  `convert` with an explicit map-composition calculation.
- `Monodromy`: makes the induced multiplicative action transparent to typeclass
  synthesis and spells out the final projection/lift equality.

The old local `SimplicialObjectHomotopy` backport is intentionally not
vendored: Mathlib v4.32 now contains the stronger upstream module
`Mathlib.AlgebraicTopology.SimplicialObject.Homotopy`.

Likewise, Mathlib v4.32 now proves that a `TopCat.Homotopy` induces a chain
homotopy on singular chains. `SingularHomologyHomotopyInvariance` preserves the
upstream public API while discharging `SingularPrismOperator` directly from
`TopCat.Homotopy.singularChainComplexFunctorObjMap`; the old custom prism and
its backports are excluded from the local dependency slice.

The same v4.32 theorem works over arbitrary coefficient modules. The vendored
cohomology homotopy-invariance layer therefore uses Mathlib's `Homotopy.op` and
`TopCat.Homotopy.singularChainComplexFunctorObjMap`, excluding the old
`PrismSimplicialHomotopy` backport. `CupProductScaffolding` reuses Mathlib's
current tensor-additivity instances and enables the same compatibility options
used by Mathlib for downward-complex tensor signs.

`Degree` now unfolds the categorical endomorphism multiplication explicitly,
and `AlexanderWhitney` applies naturality through
`ConcreteCategory.congr_hom`; these are proof-preserving v4.32 API updates.

`CoveringSimplexLift` uses the renamed `LocallyPathConnectedSpace` class, and
`DegreeAPIStrengthening` explicitly closes a post-rewrite reflexive goal.

`CupProduct` uses v4.32's `SSet.ι_chainComplexMap_f` for singular-chain
generators and explicitly closes the definitional conversions around coproduct
inclusions.

`BarycentricSubdivisionDiameter` uses the current singleton-sum identity and
direct `calc` proofs for its one-step and iterated contraction estimates.

The Alexander--Whitney face and chain-map layers use the current
`Functor.map_comp_apply` API and make coproduct-map definitional conversions
explicit under the v4.32 elaborator.

`BarycentricSubdivisionOperator` uses the renamed `continuous_finsetSum` lemma
and the same v4.32 definitional-equality compatibility settings as Mathlib's
homological-complex implementation.

`CochainCupLeibniz` is included unchanged apart from namespace isolation.
`CohomologyCupProduct` replaces fragile element-level conversions through
`forget₂` by applications of categorical morphism equalities via
`ConcreteCategory.congr_hom`.  Its cup-product and pullback statements retain
their upstream strength while elaborating cleanly with Mathlib v4.32's concrete
homology API.

`CoveringTransferChains` is included unchanged apart from namespace isolation.
`CoveringTransferBoundary` uses concrete-category naturality for face maps and
replaces the unbounded automated lift argument by an explicit two-sheet split,
lift uniqueness, and antipodal involutivity.  Its face compatibility is proved
through the simplicial naturality squares, preserving the genuine mod-two
transfer chain map.

`CupProductPowers` is included unchanged apart from namespace isolation.
`InducedOnRPCohomology` enables Mathlib's v4.32 backward definitional-equality
compatibility for the contravariant functor composition identities; all
identity, composition, naturality, and deck-transformation statements retain
their upstream formulations.

`CoveringTransferHomology` is included unchanged apart from namespace
isolation; it descends the transfer chain map and its dual to homology and
cohomology using Mathlib's current homology-map API.

`RPnW1Cochain` uses the current `LocallyPathConnectedSpace` API and evaluates
the coproduct-defined cocycle through the morphism-level `Sigma.ι_desc`
identity, avoiding a v4.32-dependent mismatch between definitionally equal
coproduct-family lambdas.

`H1ClassifierZMod2` replaces proof-sensitive conversions by the additive and
scalar Kronecker identities with explicit cocycle witnesses.  Its descent to
cohomology is proved through `homologyπ`, and the boundary-annihilation step is
an explicit categorical calculation with `toCycles_i` and `iCycles_d`.  The
surjectivity theorem and its injective-module construction are unchanged in
strength.

`KroneckerNaturality` proves the evaluation square using the current
`homologyπ_naturality` and `cyclesMap_i` morphism equalities via
`ConcreteCategory.congr_hom`.  It preserves both naturality and bijectivity of
the mod-two Kronecker classifier.

`DoubleCoverClass` is included unchanged apart from namespace isolation.
`MonodromyNontrivial` now obtains the path between antipodes directly from
`IsPathConnected.joinedIn(...).joined_subtype` and identifies monodromy with
the endpoint of the canonical lift by definition.  The resulting nontriviality
and surjectivity statements for the double-cover classifying character are
unchanged.

`MonodromyCharacter` and `ConstructRPAlpha` are included unchanged apart from
namespace isolation.  `RPnMonodromyFunctional` evaluates its coproduct-defined
defect cochain through `Sigma.ι_desc` and proves additivity of cocycle classes
by injectivity of `iCycles`, preserving the construction and odd-map invariance
of the projective degree-one class.

`ActualRPAlpha` is included unchanged apart from namespace isolation, tying the
abstractly constructed degree-one class to the concrete `w₁` cocycle.

The `RPnCupProductGenerator` and `RPAlphaEqualsModelGenerator` dependency slice
adds the equatorial-inclusion, additive cellular, cup-product/model, and
degree-one-generator layers.  The v4.32 port enables Mathlib's backward
definitional-equality compatibility where the upstream aliases for genuine
singular (co)homology elaborate with distinct inferred structure instances.
It also replaces fragile rewrites by direct linear-map, scalar-distributivity,
and `smul_mul_smul_comm` arguments; all theorem statements and topological
hypotheses retain their upstream strength.  The fundamental-loop calculation
uses the current `PiLp` simplifier API rather than the deprecated
`EuclideanSpace.norm_single` name.

`PermSignLastFaceFinished` replaces a proof-sensitive permutation factorization
conversion by pointwise evaluation on the last vertex and its `castPred`
complement.  The unit- and coefficient-valued sign identities are unchanged.

The affine internal-swap, adjacent-sign, finite-cancellation, and
`BarycentricBoundaryCancellation` modules complete the paired-term cancellation
layer.  The boundary module uses the v4.32 definitional-equality compatibility
settings and the current minimal `toSSetObjEquiv` simplifier set.

`BarycentricBoundaryChainMap` normalizes categorical composites explicitly to
nested `ModuleCat` applications, then applies the generator cancellation and
the resulting morphism identity through `ConcreteCategory.congr_hom`.

`BarycentricSubdivisionChainMap` packages those degreewise operators and their
boundary identity as a genuine singular-chain-complex endomorphism.

`BarycentricSubdivisionCone` and `BarycentricSubdivisionHomotopyOperator` are
included unchanged apart from namespace isolation.  They define the affine
cone on singular simplices and the recursive homotopy operator used to compare
the identity with barycentric subdivision.

For bounded incremental elaboration, the cone implementation is split across
private dependency modules (`ConeTailFunDef`, `ConeTailFun`, `ConeTail`,
`ConeDefs`, and `ConeGeometry`).  The public `BarycentricSubdivisionCone`
module reassembles the exact upstream declarations and imports the chain-level
dependencies only where they are first needed; no theorem statement is changed.

The geometry layer is itself split at theorem boundaries into `Continuity`,
`FaceZero`, `TailCoface`, and `FaceSucc` after the combined layer exceeded the
short MSI iteration budget.  `ConeGeometry` re-exports that chain.  This is a
pure elaboration-performance split; the declarations remain verbatim modulo the
documented Lean v4.32 compatibility edits.

The cone-on-chains layer is also split at declaration boundaries into the
simplex definitions, three face formulas, chain definitions, and three boundary
formulas.  The public `BarycentricSubdivisionCone` file re-exports the final
layer.  This avoids repeating the earlier monolithic elaboration hotspot while
preserving the upstream theorem interface.

`BarycentricSubdivisionHomotopyFormula` and
`BarycentricSubdivisionChainHomotopy` are included unchanged apart from
namespace isolation.  They prove the degreewise homotopy identity and package
it as a chain homotopy.

`BarycentricSubdivisionIter` is included unchanged apart from namespace
isolation; it constructs the accumulated homotopy for every iterate of
barycentric subdivision.

The small-simplices foundation (`SmallSimplices`, `SmallChains`,
`SmallChainComplex`, and `SingularSimplexLebesgueNumber`) is included unchanged
apart from namespace isolation.  It defines the open-cover subcomplex and the
compact-simplex Lebesgue-number input used by the iterated-subdivision argument.

The iterated-subdivision small-chain layer is included unchanged apart from
namespace isolation.  It proves that sufficiently iterated subdivision is
subordinate to an open cover, keeps the accumulated homotopy subordinate, and
deduces the small-chain inclusion is a homology isomorphism.

The subordinate-chain projection and Mayer--Vietoris layers are included
unchanged apart from namespace isolation.  They construct the short exact
sequence for a two-set cover and its induced long exact homology sequence.

The sphere-homology bridge now also includes the top-homology reduction,
reduced-to-unreduced comparison, ball-boundary long exact sequence,
subchain/subspace comparison, and Mayer--Vietoris suspension step.  These five
modules are copied unchanged apart from namespace isolation and form the next
exact dependency chain toward the unconditional odd-degree theorem.

The following sphere calculation layer is likewise included without theorem
changes: singular degree-zero homology, its path-connected and componentwise
forms, the Mayer--Vietoris calculation of `S¹`, the suspension tower, and the
resulting positive sphere orientation.  Together these discharge the concrete
sphere-homology orientation input later used by Borsuk--Ulam.

`SphereModTwoHomologyVanishing` retains the upstream theorem statements.  Its
single implementation-level port replaces the v4.28 project-local prism
backport by Mathlib v4.32's
`TopCat.Homotopy.singularChainComplexFunctorObjMap`; this avoids carrying a
dead compatibility cone while proving the identical coefficient-general
homotopy invariance used by the sphere calculation.

The RPⁿ dimension-vanishing slice is staged in its original dependency order:
Hausdorffness and the filtration/cofiber package, homology notation and sphere
above-dimension vanishing, affine-chart deformations, the RPⁿ
Mayer--Vietoris step, and the resulting homology/cohomology vanishing theorem.
All declarations in this slice are unchanged apart from namespace isolation.

The coefficient-reduction branch is staged through its unconditional endpoint:
the canonical sphere comparison, integral-to-mod-two reduction, rank-one and
Kronecker actions, concrete mod-two top class and Bockstein constructions, and
`OddDegreeTheoremBranch2Discharged`.  These modules retain the exact upstream
statements and proofs apart from namespace isolation.

The transfer/Gysin base is staged through transfer naturality and
nonvanishing, the transfer short exact sequence and surjectivity, the Gysin
connecting map and cup formula, and the actual-α top-power and top-class
assemblies.  These declarations are copied unchanged apart from namespace
isolation.

The final staged source slice contains the cellular cup-product comparison,
the branch-3 generator identification, the branch-4 transfer witnesses and
nonvanishing theorem, both unconditional final assemblies, the unconditional
odd-degree theorem, and `BorsukUlam.borsuk_ulam`.  Apart from removing stale
root-namespace qualifiers after isolation, their theorem statements and proofs
are unchanged from the pinned upstream commit.

`ComplexOddMapCommonZero` is the local adapter from the vendored real-coordinate
Borsuk--Ulam theorem to finite complex coordinate spaces.  It realifies and
zero-pads the coordinates, so it introduces no additional topological input.
