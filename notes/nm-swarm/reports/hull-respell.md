# hull-respell lane report

## Scope
The relator re-spelling of Hull's Theorem 7.1 at Osin's Theorem 2.4. The job is to remove the
family-form admission and the re-spelling input from the manuscript quotient field
`Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement`, so that it rests only on the two geometric
leaves.

## Compiled on main (probe 0911-211417-50221 GREEN, last landing 3832abdb7)
All 20 lane files on main match the bytes of that probe.
- C1, the un-coned joint image: `GGT.cyclicPeripheralRemovalStatement : CyclicPeripheralRemovalStatement`.
  It is closed (`#audit_closed_axioms`) and lives in GGT/HullSCUnconeThin. It builds over GGT/HullSCUncone{Expansion, ClosingJump,
  CosetAvoidance, TriangleConnectors, PathPoints, CosetCoordinates, LemmaA, Walk, LemmaB, Sides} and
  GGT/HullSCCyclicPeripheralRemoval.
- C2, bounded joint re-spelling at Hull's published relator:
  `HullSC.exists_publishedRelator_boundedJointRespelling`, in GGT/HullSCLemma44BoundedJointRespellingHullRelator.
- C3, Osin's Theorem 2.4 at the published relator from the bounded leaves:
  `GGT.RelHyp.osin24HullStep_of_boundedLeaves`, in GGT/RelHypOsin24PublishedHullStep. It is consumed by
  `fournierFacioQuotientStatement_of_hullStep` (GGT/RelHypProp23FromHullStep).
- The image form of Osin's Lemma 5.1 from the least-area certificate:
  `HullSC.boundedImageEmbeddingStatement_of_quasiGeodesicLeastArea`, in GGT/HullSCBoundedImageEmbeddingLeastArea.
- The quotient field over the least-area leaves, in GGT/RelHypProp23FromLeastAreaLeaves:
  ```lean
  theorem GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves
      (hgreendlinger :
        GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
      (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
      Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement
  ```
  It is consumed by `Manuscript.NonMF.TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`
  (field `smallCancellationQuotient`).
- Census: `metadata/nm-census-rows/hull-respell.tsv`, row LINE:1675, `partial`. The status is partial
  because of the two leaves below.

## Open leaves (other lanes)
1. `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (OsinAppendixSections) is the least-area
   Greendlinger waist. Its producer on main is
   `relativeGreendlingerQuasiGeodesicLeastArea_of_inputs (hO52 : O52LeastAreaStatement)
   (h94 : OsinLemma94SectionStatement) (hin : OsinSection97InputsStatement)` (OsinAppendixAssembly).
   `o52LeastArea` closes `hO52`. The open inputs are:
   - `OsinLemma94SectionStatement`, owned by hull-unbound.
   - `OsinSection97InputsStatement`, the conjunction `MultipleEdgeCutInput ∧ LoopCutInput ∧ EulerCountInput ∧ DescentInput`
     for every eps0 ≤ eps and rho0 ≤ rho. These belong to hull-select (cuts), hull-euler (Euler count) and dgo-analytic (descent).
2. `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` (HullSCLemma51EmbeddedBridge) is Osin's
   Lemma 5.1 in embedded form. It is owned by hull-bridge and hull-component, via the letter pullback.

## Relaunch 2026-09-12
- The relaunch directive gave this lane "E1–E6" and `phiSubdividedGraph`. Those are the six
  GGT/VanKampen/Estimating/OsinAppendixEuler* modules, which belong to hull-euler. That lane is live and owns them. hull-respell
  edited none of them.
- There were no stranded edits: every hull-respell file in the shared tree matches origin/main, and the attic copies are
  superseded.
- One batch probe of the six Euler modules ran under hull-euler's lane name (0912-092011-96837) and FAILED
  in OsinAppendixEulerSubdivided:
  - Five unused simp arguments at line 71.
  - Theorems in `namespace SubdividedGraph` whose statements never mention the section variable
    `S` (`facePerm_ne`, `facePerm_three_ne`, `facePerm_five_ne`, `facePerm_two_ne`,
    `six_le_faceDegree_of_subdividedGraph`). Lean 4 leaves such variables out, so `S.*` is unknown inside
    their proofs. The fix is `include S in` or an explicit binder.
  - The other five modules did not build.
  This diagnosis went to hull-euler.
- The scope of this lane is finished. The statements the least-area endpoint consumes went to hull-select.
