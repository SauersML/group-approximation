# HamSandwich v4.32 port: transitive import order (2026-09-05)

Machine-derived from the actual `import` lines of all 199 `.lean` files under
`GroupApproximation/ThirdParty/HamSandwich/`, not from filenames or memory.

## Structural findings

- **199** modules, **0** import cycles (Tarjan SCC over the internal import graph:
  every strongly connected component is a singleton).
- **0** dangling internal imports: every `import GroupApproximation.ThirdParty.HamSandwich.*`
  line resolves to a file that exists in the tree.
- Longest import chain: **57** modules (depth 0 through 56).
- Single sink: `SphereOddDegree.ComplexOddMapCommonZero` (depth 56). Building it
  builds all 199. `SphereOddDegree.BorsukUlam` (depth 55) builds 198 of them.
- Six sources (depth 0, no internal imports):
  - `SphereOddDegree.AlgebraicTopology.AffineBarycentricSubdivision`
  - `SphereOddDegree.AlgebraicTopology.BarycentricFiniteCancellation`
  - `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionDiameter`
  - `SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy`
  - `SphereOddDegree.Basic`
  - `SphereOddDegree.RPnCohomologyRingModel`

## How to use this

`scripts/remote-build.sh <Mod>` builds `<Mod>` and its transitive imports. The
script takes ONE positional argument, but interpolates it unquoted into the remote
`lake build $BUILD_TARGETS`, so a single space-separated quoted string batches
several targets under one fleet-mutex acquisition:

```sh
scripts/remote-build.sh "GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Basic \
  GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Antipodal"
```

Prefix every name below with `GroupApproximation.ThirdParty.HamSandwich.`.

## Lane ownership

`A` = lane `hamsandwich-port-A` (foundations). `B` = lane `hamsandwich-port-B`
(Final/, Branch3*, Branch4*, AlgebraicTopology/, BorsukUlam, DegreeAPIStrengthening,
ComplexOddMapRealification). `-` = not named in either lane brief; whoever hits it
first should claim it in this file. Note the one overlap the briefs create:
`AlgebraicTopology/{AffineBarycentricSubdivision, HomotopyToChainHomotopy,
SingularHomologyFunctorAPI, SingularHomologyHomotopyInvariance}` are named in lane A's
grant but sit inside the directory lane B is told to own; the specific grant is taken
to win, so they are marked `A`.

## Layered topological order

Layer `d` = longest path from a source. Every module's imports have strictly
smaller depth, so the layers may be built in order and modules within one layer
are mutually independent (safe to batch into a single `lake build`).


### Layer 0

- [A] `SphereOddDegree.AlgebraicTopology.AffineBarycentricSubdivision`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricFiniteCancellation`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionDiameter`
- [A] `SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy`
- [A] `SphereOddDegree.Basic`
- [A] `SphereOddDegree.RPnCohomologyRingModel`

### Layer 1

- [B] `SphereOddDegree.AlgebraicTopology.AffineInternalSwapLemmas`
- [B] `SphereOddDegree.AlgebraicTopology.AffineLastFaceIdentity`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFunDef`
- [B] `SphereOddDegree.AlgebraicTopology.HomotopyInvariance`
- [A] `SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI`
- [A] `SphereOddDegree.Antipodal`
- [B] `SphereOddDegree.ComplexOddMapRealification`
- [A] `SphereOddDegree.TopCatBridge`

### Layer 2

- [B] `SphereOddDegree.AlgebraicTopology.AffineInternalSwapFace`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFun`
- [B] `SphereOddDegree.AlgebraicTopology.Degree`
- [B] `SphereOddDegree.AlgebraicTopology.SingularCohomology`
- [A] `SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance`
- [A] `SphereOddDegree.RealProjectiveSpace`

### Layer 3

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTail`
- [B] `SphereOddDegree.AlgebraicTopology.CupProductScaffolding`
- [B] `SphereOddDegree.AlgebraicTopology.SingularCohomologyHomotopyInvariance`
- [A] `SphereOddDegree.Covering`
- [-] `SphereOddDegree.Hausdorff`
- [A] `SphereOddDegree.RPnLowDimensional`
- [A] `SphereOddDegree.RealProjectiveSpaceInclusion`

### Layer 4

- [B] `SphereOddDegree.AlgebraicTopology.AlexanderWhitney`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeDefs`
- [A] `SphereOddDegree.Monodromy`
- [-] `SphereOddDegree.SphereTopHomology`

### Layer 5

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeContinuity`
- [B] `SphereOddDegree.AlgebraicTopology.CoveringSimplexLift`
- [B] `SphereOddDegree.AlgebraicTopology.CupProduct`
- [B] `SphereOddDegree.DegreeAPIStrengthening`
- [-] `SphereOddDegree.SphereTopHomologyReduction`

### Layer 6

- [B] `SphereOddDegree.AlgebraicTopology.AlexanderWhitneyFaceMaps`
- [B] `SphereOddDegree.AlgebraicTopology.CoveringTransferChains`
- [B] `SphereOddDegree.AlgebraicTopology.CupProductPowers`
- [-] `SphereOddDegree.DegreeFunctorialityAndHomotopy`
- [A] `SphereOddDegree.ReducedToUnreducedSphereTopHomology`

### Layer 7

- [B] `SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap`
- [-] `SphereOddDegree.AntipodalDegree`
- [-] `SphereOddDegree.BallBoundaryLES`

### Layer 8

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionOperator`
- [B] `SphereOddDegree.AlgebraicTopology.CochainCupLeibniz`
- [B] `SphereOddDegree.AlgebraicTopology.CoveringTransferBoundary`
- [-] `SphereOddDegree.ModTwoDegreeComparison`
- [A] `SphereOddDegree.SphereModelTransport`

### Layer 9

- [B] `SphereOddDegree.AlgebraicTopology.CohomologyCupProduct`
- [B] `SphereOddDegree.AlgebraicTopology.PermSignAdjacentSwap`
- [B] `SphereOddDegree.AlgebraicTopology.PermSignLastFaceFinished`

### Layer 10

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation`
- [B] `SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2`
- [B] `SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology`
- [A] `SphereOddDegree.RPnW1Cochain`

### Layer 11

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricBoundaryChainMap`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroCoordinate`
- [B] `SphereOddDegree.AlgebraicTopology.CoveringTransferHomology`
- [B] `SphereOddDegree.AlgebraicTopology.KroneckerNaturality`
- [B] `SphereOddDegree.AlgebraicTopology.SmallSimplices`
- [A] `SphereOddDegree.DoubleCoverClass`
- [A] `SphereOddDegree.RPnInclusionCohomology`
- [A] `SphereOddDegree.RPnTopClassAlphaPower`

### Layer 12

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainMap`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroTail`
- [B] `SphereOddDegree.AlgebraicTopology.SingularSimplexLebesgueNumber`
- [B] `SphereOddDegree.AlgebraicTopology.SmallChains`
- [-] `SphereOddDegree.MonodromyNontrivial`
- [A] `SphereOddDegree.RPnAdditiveCohomology`
- [A] `SphereOddDegree.RPnCohomologyRingBridge`
- [A] `SphereOddDegree.RPnFiltrationGeometry`
- [A] `SphereOddDegree.RPnTopClassTransferNaturality`
- [A] `SphereOddDegree.RPnTopClassTransferNonzero`

### Layer 13

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZero`
- [B] `SphereOddDegree.AlgebraicTopology.CoveringTransferSES`
- [B] `SphereOddDegree.AlgebraicTopology.SmallChainComplex`
- [A] `SphereOddDegree.MonodromyCharacter`
- [A] `SphereOddDegree.RPnFiltrationCofiber`
- [A] `SphereOddDegree.RPnRelativeCohomologyOneCell`

### Layer 14

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailCoface`
- [B] `SphereOddDegree.AlgebraicTopology.SubordinateChains`
- [A] `SphereOddDegree.ConstructRPAlpha`
- [A] `SphereOddDegree.RPnCellularCochainStructure`
- [A] `SphereOddDegree.RPnCellularFiltration`
- [A] `SphereOddDegree.RPnTopClassTransferSurjective`

### Layer 15

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceSucc`
- [B] `SphereOddDegree.AlgebraicTopology.CoordinateProjection`
- [-] `SphereOddDegree.FinalOddMapComparison`
- [A] `SphereOddDegree.RPnCellularCochain`
- [A] `SphereOddDegree.RPnCupProductGenerator`
- [A] `SphereOddDegree.RPnGysinConnecting`
- [A] `SphereOddDegree.RPnMonodromyFunctional`
- [A] `SphereOddDegree.RPnSingularToCellularComparison`

### Layer 16

- [A] `SphereOddDegree.ActualRPAlpha`
- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeGeometry`
- [B] `SphereOddDegree.AlgebraicTopology.CoefficientReduction`
- [B] `SphereOddDegree.AlgebraicTopology.KroneckerTopClassAction`
- [A] `SphereOddDegree.RPnActualAlphaPowerNonvanishing`
- [A] `SphereOddDegree.RPnCellularCupProduct`
- [A] `SphereOddDegree.RPnGeneratorIdentificationTarget`
- [A] `SphereOddDegree.RPnGysinConnectingInjective`

### Layer 17

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexDefs`
- [B] `SphereOddDegree.AlgebraicTopology.Branch2IntegralDegreeAction`
- [B] `SphereOddDegree.AlgebraicTopology.Branch2RankOne`
- [B] `SphereOddDegree.AlgebraicTopology.ConstructModTwoTopClassComparison`
- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoCoeffBridge`
- [A] `SphereOddDegree.RPnCellularDiagonal`
- [A] `SphereOddDegree.RPnCupProductModelCompatibility`
- [A] `SphereOddDegree.RPnTopClassTransferAssembly`
- [A] `SphereOddDegree.RPnW1ClassEqActualRPAlpha`

### Layer 18

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceZero`
- [B] `SphereOddDegree.AlgebraicTopology.Branch2CoefficientReduction`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferAPI`
- [A] `SphereOddDegree.RPnCupProductStructureConstruction`
- [A] `SphereOddDegree.RPnDegreeOneGenerator`
- [A] `SphereOddDegree.RPnGysinConnectingCupLift`

### Layer 19

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceSucc`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferTopClass`
- [A] `SphereOddDegree.RPAlphaEqualsModelGenerator`
- [A] `SphereOddDegree.RPnCupProductNonvanishingTarget`
- [A] `SphereOddDegree.RPnGysinConnectingCupFaces`
- [A] `SphereOddDegree.RPnSingularCellularCupComparison`

### Layer 20

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceOneZero`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferNonzero`
- [A] `SphereOddDegree.RPnActualAlphaPowersGenerate`
- [A] `SphereOddDegree.RPnCupProductNonvanishing`
- [A] `SphereOddDegree.RPnGysinConnectingCupW1Lift`

### Layer 21

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeChainDefs`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferWitness`
- [A] `SphereOddDegree.RPnGeneratorIdentification`
- [A] `SphereOddDegree.RPnGysinConnectingCupW1Back`

### Layer 22

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundaryZero`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4RPnTopClassTransfer`
- [A] `SphereOddDegree.RPnGysinConnectingCupMaps`

### Layer 23

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundarySucc`
- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferNonvanishing`
- [A] `SphereOddDegree.RPnGysinConnectingCupIdentities`

### Layer 24

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundaryLinear`
- [A] `SphereOddDegree.RPnGysinConnectingCup`

### Layer 25

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone`

### Layer 26

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyOperator`

### Layer 27

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula`

### Layer 28

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainHomotopy`

### Layer 29

- [B] `SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionIter`

### Layer 30

- [B] `SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex`

### Layer 31

- [B] `SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallChains`

### Layer 32

- [B] `SphereOddDegree.AlgebraicTopology.IteratedSubdivisionHomotopySmall`
- [B] `SphereOddDegree.AlgebraicTopology.SmallChainsHomologySurjectivity`

### Layer 33

- [B] `SphereOddDegree.AlgebraicTopology.SmallChainsHomologyInjectivity`

### Layer 34

- [B] `SphereOddDegree.AlgebraicTopology.SmallChainsQuasiIso`

### Layer 35

- [B] `SphereOddDegree.AlgebraicTopology.MayerVietorisSES`

### Layer 36

- [B] `SphereOddDegree.AlgebraicTopology.MayerVietoris`

### Layer 37

- [B] `SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge`

### Layer 38

- [B] `SphereOddDegree.AlgebraicTopology.SingularH0`
- [B] `SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep`

### Layer 39

- [B] `SphereOddDegree.AlgebraicTopology.SingularH0PathConnected`

### Layer 40

- [B] `SphereOddDegree.AlgebraicTopology.SingularH0General`
- [B] `SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV`

### Layer 41

- [B] `SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMV`
- [A] `SphereOddDegree.SphereModTwoHomologyVanishing`

### Layer 42

- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoOneBase`
- [B] `SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV`
- [A] `SphereOddDegree.RPnGysinConnectingInjectiveLt`
- [A] `SphereOddDegree.RPnHomologyNotation`
- [-] `SphereOddDegree.SphereModTwoHomologyAboveDimension`

### Layer 43

- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoBockstein`
- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoTopClass`
- [B] `SphereOddDegree.Final.FinalAssumptionAliases`
- [-] `SphereOddDegree.FinalOddMapComparisonUnconditionalSphere`
- [A] `SphereOddDegree.RPnActualAlphaPowerNoCup`
- [A] `SphereOddDegree.RPnAffineCover`

### Layer 44

- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoTopGeneratorData`
- [B] `SphereOddDegree.Final.OddDegreeTheorem`
- [A] `SphereOddDegree.RPnActualAlphaPowerEqGeneratorNoCup`
- [A] `SphereOddDegree.RPnDeletedNorthSphereDeformation`

### Layer 45

- [B] `SphereOddDegree.AlgebraicTopology.SphereModTwoTopDegreeAction`
- [B] `SphereOddDegree.AlgebraicTopology.SphereTopCohomologyRankOne`
- [B] `SphereOddDegree.Final.OddDegreeTheoremCanonical`
- [A] `SphereOddDegree.RPnDeletedNorthProjectiveMaps`
- [A] `SphereOddDegree.RPnGeneratorCupNoCup`

### Layer 46

- [B] `SphereOddDegree.AlgebraicTopology.ModTwoTopClassComparisonUnconditional`
- [A] `SphereOddDegree.RPnCupProductStructureFinal`
- [A] `SphereOddDegree.RPnDeletedNorthProjectiveHomotopy`

### Layer 47

- [B] `SphereOddDegree.Branch3RPnGeneratorIdentificationFromCellular`
- [B] `SphereOddDegree.Final.OddDegreeTheoremBranch2Discharged`
- [A] `SphereOddDegree.RPnAffineCellContractible`

### Layer 48

- [B] `SphereOddDegree.Branch34OddMapFixesTopClassAssembly`
- [A] `SphereOddDegree.RPnActualTopPowerFinalAssembly`
- [A] `SphereOddDegree.RPnAffineOverlapSphere`

### Layer 49

- [B] `SphereOddDegree.AlgebraicTopology.Branch4TransferNonvanishingUnconditional`
- [A] `SphereOddDegree.RPnMayerVietorisSpecial`

### Layer 50

- [A] `SphereOddDegree.RPnHomologyDimensionVanishing`

### Layer 51

- [A] `SphereOddDegree.RPnCohomologyDimensionVanishing`

### Layer 52

- [B] `SphereOddDegree.Final.OddMapFixesTopClassUnconditional`

### Layer 53

- [B] `SphereOddDegree.Final.FinalUnconditional`

### Layer 54

- [B] `SphereOddDegree.Final.OddDegreeTheoremUnconditional`

### Layer 55

- [B] `SphereOddDegree.BorsukUlam`

### Layer 56

- [-] `SphereOddDegree.ComplexOddMapCommonZero`

## Strict linear order

A single valid sequential order (Kahn, ties broken alphabetically), for when a
strictly one-at-a-time walk is wanted:

```text
  1  SphereOddDegree.AlgebraicTopology.AffineBarycentricSubdivision
  2  SphereOddDegree.AlgebraicTopology.AffineInternalSwapLemmas
  3  SphereOddDegree.AlgebraicTopology.AffineInternalSwapFace
  4  SphereOddDegree.AlgebraicTopology.AffineLastFaceIdentity
  5  SphereOddDegree.AlgebraicTopology.BarycentricFiniteCancellation
  6  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFunDef
  7  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailFun
  8  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTail
  9  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeDefs
 10  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeContinuity
 11  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionDiameter
 12  SphereOddDegree.AlgebraicTopology.HomotopyToChainHomotopy
 13  SphereOddDegree.AlgebraicTopology.HomotopyInvariance
 14  SphereOddDegree.AlgebraicTopology.SingularHomologyFunctorAPI
 15  SphereOddDegree.AlgebraicTopology.SingularCohomology
 16  SphereOddDegree.AlgebraicTopology.CupProductScaffolding
 17  SphereOddDegree.AlgebraicTopology.AlexanderWhitney
 18  SphereOddDegree.AlgebraicTopology.CupProduct
 19  SphereOddDegree.AlgebraicTopology.AlexanderWhitneyFaceMaps
 20  SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap
 21  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionOperator
 22  SphereOddDegree.AlgebraicTopology.CochainCupLeibniz
 23  SphereOddDegree.AlgebraicTopology.CohomologyCupProduct
 24  SphereOddDegree.AlgebraicTopology.CupProductPowers
 25  SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2
 26  SphereOddDegree.AlgebraicTopology.KroneckerNaturality
 27  SphereOddDegree.AlgebraicTopology.PermSignAdjacentSwap
 28  SphereOddDegree.AlgebraicTopology.PermSignLastFaceFinished
 29  SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation
 30  SphereOddDegree.AlgebraicTopology.BarycentricBoundaryChainMap
 31  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
 32  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroCoordinate
 33  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroTail
 34  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZero
 35  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeTailCoface
 36  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceSucc
 37  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeGeometry
 38  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexDefs
 39  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceZero
 40  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceSucc
 41  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeSimplexFaceOneZero
 42  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeChainDefs
 43  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundaryZero
 44  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundarySucc
 45  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeBoundaryLinear
 46  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone
 47  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyOperator
 48  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula
 49  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainHomotopy
 50  SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionIter
 51  SphereOddDegree.AlgebraicTopology.SingularCohomologyHomotopyInvariance
 52  SphereOddDegree.AlgebraicTopology.SingularHomologyHomotopyInvariance
 53  SphereOddDegree.AlgebraicTopology.SmallSimplices
 54  SphereOddDegree.AlgebraicTopology.SingularSimplexLebesgueNumber
 55  SphereOddDegree.AlgebraicTopology.SmallChains
 56  SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
 57  SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
 58  SphereOddDegree.AlgebraicTopology.IteratedSubdivisionHomotopySmall
 59  SphereOddDegree.AlgebraicTopology.SmallChainComplex
 60  SphereOddDegree.AlgebraicTopology.SmallChainsHomologySurjectivity
 61  SphereOddDegree.AlgebraicTopology.SmallChainsHomologyInjectivity
 62  SphereOddDegree.AlgebraicTopology.SmallChainsQuasiIso
 63  SphereOddDegree.AlgebraicTopology.SubordinateChains
 64  SphereOddDegree.AlgebraicTopology.CoordinateProjection
 65  SphereOddDegree.AlgebraicTopology.MayerVietorisSES
 66  SphereOddDegree.AlgebraicTopology.MayerVietoris
 67  SphereOddDegree.Basic
 68  SphereOddDegree.Antipodal
 69  SphereOddDegree.ComplexOddMapRealification
 70  SphereOddDegree.RPnCohomologyRingModel
 71  SphereOddDegree.RealProjectiveSpace
 72  SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
 73  SphereOddDegree.Covering
 74  SphereOddDegree.Hausdorff
 75  SphereOddDegree.Monodromy
 76  SphereOddDegree.AlgebraicTopology.CoveringSimplexLift
 77  SphereOddDegree.AlgebraicTopology.CoveringTransferChains
 78  SphereOddDegree.AlgebraicTopology.CoveringTransferBoundary
 79  SphereOddDegree.AlgebraicTopology.CoveringTransferHomology
 80  SphereOddDegree.DoubleCoverClass
 81  SphereOddDegree.MonodromyNontrivial
 82  SphereOddDegree.MonodromyCharacter
 83  SphereOddDegree.ConstructRPAlpha
 84  SphereOddDegree.RPnLowDimensional
 85  SphereOddDegree.RPnTopClassAlphaPower
 86  SphereOddDegree.RPnCohomologyRingBridge
 87  SphereOddDegree.RPnTopClassTransferNaturality
 88  SphereOddDegree.AlgebraicTopology.CoveringTransferSES
 89  SphereOddDegree.RPnTopClassTransferNonzero
 90  SphereOddDegree.RPnW1Cochain
 91  SphereOddDegree.RPnMonodromyFunctional
 92  SphereOddDegree.ActualRPAlpha
 93  SphereOddDegree.RPnW1ClassEqActualRPAlpha
 94  SphereOddDegree.RealProjectiveSpaceInclusion
 95  SphereOddDegree.RPnInclusionCohomology
 96  SphereOddDegree.RPnAdditiveCohomology
 97  SphereOddDegree.RPnCupProductGenerator
 98  SphereOddDegree.RPnFiltrationGeometry
 99  SphereOddDegree.RPnFiltrationCofiber
100  SphereOddDegree.RPnCellularFiltration
101  SphereOddDegree.RPnCellularCochain
102  SphereOddDegree.RPnCellularCupProduct
103  SphereOddDegree.RPnCellularDiagonal
104  SphereOddDegree.RPnGeneratorIdentificationTarget
105  SphereOddDegree.RPnRelativeCohomologyOneCell
106  SphereOddDegree.RPnCellularCochainStructure
107  SphereOddDegree.RPnSingularToCellularComparison
108  SphereOddDegree.RPnCupProductModelCompatibility
109  SphereOddDegree.RPnCupProductStructureConstruction
110  SphereOddDegree.RPnCupProductNonvanishingTarget
111  SphereOddDegree.RPnDegreeOneGenerator
112  SphereOddDegree.RPAlphaEqualsModelGenerator
113  SphereOddDegree.RPnActualAlphaPowersGenerate
114  SphereOddDegree.RPnSingularCellularCupComparison
115  SphereOddDegree.RPnCupProductNonvanishing
116  SphereOddDegree.RPnTopClassTransferSurjective
117  SphereOddDegree.RPnGysinConnecting
118  SphereOddDegree.RPnGysinConnectingCupLift
119  SphereOddDegree.RPnGysinConnectingCupFaces
120  SphereOddDegree.RPnGysinConnectingCupW1Lift
121  SphereOddDegree.RPnGysinConnectingCupW1Back
122  SphereOddDegree.RPnGysinConnectingCupMaps
123  SphereOddDegree.RPnGysinConnectingCupIdentities
124  SphereOddDegree.RPnGysinConnectingCup
125  SphereOddDegree.RPnGysinConnectingInjective
126  SphereOddDegree.TopCatBridge
127  SphereOddDegree.AlgebraicTopology.Degree
128  SphereOddDegree.SphereTopHomology
129  SphereOddDegree.DegreeAPIStrengthening
130  SphereOddDegree.DegreeFunctorialityAndHomotopy
131  SphereOddDegree.AntipodalDegree
132  SphereOddDegree.ModTwoDegreeComparison
133  SphereOddDegree.FinalOddMapComparison
134  SphereOddDegree.AlgebraicTopology.CoefficientReduction
135  SphereOddDegree.AlgebraicTopology.Branch2IntegralDegreeAction
136  SphereOddDegree.AlgebraicTopology.Branch2RankOne
137  SphereOddDegree.AlgebraicTopology.Branch2CoefficientReduction
138  SphereOddDegree.AlgebraicTopology.KroneckerTopClassAction
139  SphereOddDegree.AlgebraicTopology.ConstructModTwoTopClassComparison
140  SphereOddDegree.AlgebraicTopology.SphereModTwoCoeffBridge
141  SphereOddDegree.RPnActualAlphaPowerNonvanishing
142  SphereOddDegree.RPnGeneratorIdentification
143  SphereOddDegree.RPnTopClassTransferAssembly
144  SphereOddDegree.AlgebraicTopology.Branch4TransferAPI
145  SphereOddDegree.AlgebraicTopology.Branch4TransferTopClass
146  SphereOddDegree.AlgebraicTopology.Branch4TransferNonzero
147  SphereOddDegree.AlgebraicTopology.Branch4TransferWitness
148  SphereOddDegree.AlgebraicTopology.Branch4RPnTopClassTransfer
149  SphereOddDegree.AlgebraicTopology.Branch4TransferNonvanishing
150  SphereOddDegree.SphereTopHomologyReduction
151  SphereOddDegree.ReducedToUnreducedSphereTopHomology
152  SphereOddDegree.BallBoundaryLES
153  SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
154  SphereOddDegree.AlgebraicTopology.SingularH0
155  SphereOddDegree.AlgebraicTopology.SingularH0PathConnected
156  SphereOddDegree.AlgebraicTopology.SingularH0General
157  SphereOddDegree.AlgebraicTopology.SphereHomologyMVStep
158  SphereOddDegree.AlgebraicTopology.SphereHomologyS1BaseMV
159  SphereOddDegree.AlgebraicTopology.SphereSuspensionTowerFromMV
160  SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV
161  SphereOddDegree.AlgebraicTopology.SphereModTwoBockstein
162  SphereOddDegree.Final.FinalAssumptionAliases
163  SphereOddDegree.FinalOddMapComparisonUnconditionalSphere
164  SphereOddDegree.Final.OddDegreeTheorem
165  SphereOddDegree.Final.OddDegreeTheoremCanonical
166  SphereOddDegree.SphereModTwoHomologyVanishing
167  SphereOddDegree.AlgebraicTopology.SphereModTwoOneBase
168  SphereOddDegree.RPnGysinConnectingInjectiveLt
169  SphereOddDegree.RPnActualAlphaPowerNoCup
170  SphereOddDegree.RPnActualAlphaPowerEqGeneratorNoCup
171  SphereOddDegree.RPnGeneratorCupNoCup
172  SphereOddDegree.RPnCupProductStructureFinal
173  SphereOddDegree.Branch3RPnGeneratorIdentificationFromCellular
174  SphereOddDegree.Branch34OddMapFixesTopClassAssembly
175  SphereOddDegree.RPnHomologyNotation
176  SphereOddDegree.SphereModTwoHomologyAboveDimension
177  SphereOddDegree.RPnAffineCover
178  SphereOddDegree.RPnDeletedNorthSphereDeformation
179  SphereOddDegree.RPnDeletedNorthProjectiveMaps
180  SphereOddDegree.RPnDeletedNorthProjectiveHomotopy
181  SphereOddDegree.RPnAffineCellContractible
182  SphereOddDegree.RPnAffineOverlapSphere
183  SphereOddDegree.RPnMayerVietorisSpecial
184  SphereOddDegree.RPnHomologyDimensionVanishing
185  SphereOddDegree.RPnCohomologyDimensionVanishing
186  SphereOddDegree.SphereModelTransport
187  SphereOddDegree.AlgebraicTopology.SphereModTwoTopClass
188  SphereOddDegree.AlgebraicTopology.SphereModTwoTopGeneratorData
189  SphereOddDegree.AlgebraicTopology.Branch4TransferNonvanishingUnconditional
190  SphereOddDegree.AlgebraicTopology.SphereModTwoTopDegreeAction
191  SphereOddDegree.AlgebraicTopology.ModTwoTopClassComparisonUnconditional
192  SphereOddDegree.AlgebraicTopology.SphereTopCohomologyRankOne
193  SphereOddDegree.Final.OddDegreeTheoremBranch2Discharged
194  SphereOddDegree.RPnActualTopPowerFinalAssembly
195  SphereOddDegree.Final.OddMapFixesTopClassUnconditional
196  SphereOddDegree.Final.FinalUnconditional
197  SphereOddDegree.Final.OddDegreeTheoremUnconditional
198  SphereOddDegree.BorsukUlam
199  SphereOddDegree.ComplexOddMapCommonZero
```
