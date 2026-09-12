import GroupApproximation.GGT.KazhdanHypGirthEightTorsionExtraction
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.GGT.VanKampen.CombMapGluing

/-!
# Generic producers for the power-disc operations

This file records the two geometric interfaces which are independent of the
finite `W(8)` table.  A cactus fold is supplied one cell at a time, and a
fold chain is iterated by the area index.  For the seam, the source supplies
an actual exposed mate and the finite incidence maps; the constructor then
builds the Euler certificate used by the torsion extraction module.
-/

namespace GroupApproximation
namespace GGT

open TriangularHodgeLayer
open GroupApproximation.KazhdanHyp
open VanKampen
open VanKampen.SeamGluing
open VanKampen.SeamGluing.Pairing
open GirthEightTorsionExtraction
open GirthEightPrimitives2
open GirthEightVKInterface

universe u w v

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → Triangle Generator}

/-! ## Cactus folds -/

/-- A one-cell free-base fold at a literal power.  The region and endpoint
reclosure are concrete `Surgery.MapCollapse` data; `before_power` and
`after_power` are the two boundary-word calculations, while
`innerFaceCount_drop` is the exact area calculation. -/
def CactusPowerFoldStepSource : Prop :=
  ∀ (g : Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (SignedGenerator Generator)),
      PresentedGroup.mk (relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta : DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.toCombMap.IsPlanar ∧
        ∃ C : CactusBaseCellFoldData Delta,
          C.powerWord = word.map signedFreeRelLetter ∧
          C.exponent = n

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The landed fold data is a concrete constructor for the exact
`CactusBaseCellDeletionForPower` producer.  The first two conclusions are
the unchanged boundary power and the last is the exact one-cell area drop. -/
theorem cactusBaseCellDeletionForPower_of_foldStepSource
    (hsource : CactusPowerFoldStepSource (T := T)) :
    CactusBaseCellDeletionForPower T := by
  rw [CactusPowerFoldStepSource] at hsource
  intro g n hn hpow hne word hword
  obtain ⟨Delta, hplanar, C, hCword, hCn⟩ :=
    hsource g n hn hpow hne word hword
  refine ⟨Delta, hplanar, C.toDeletion, ?_⟩
  simpa [hCword, hCn] using C.boundary_power_preserved

/-- A power-fold chain source.  Each step is a concrete landed
`CactusBaseCellDeletion`; the chain index is the number of deleted base
cells, so induction on it gives the strong area induction used in the
cactus argument.

The area-drop conjunct is stated as the literal proposition
`Next.innerFaceCount + k = Delta.innerFaceCount` rather than as
`chain.innerFaceCount_eq_add_length` -- the latter is a proof term (that
theorem is unconditional, proved by induction with no hypotheses), so it
cannot sit on the left of `∧`. The asserted content is unchanged: it is
exactly what that theorem proves, for the same `chain`. -/
def CactusPowerFoldChainSource : Prop :=
  ∀ (g : Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (SignedGenerator Generator)),
      PresentedGroup.mk (relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta Next : DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.toCombMap.IsPlanar ∧ Delta.Reduced ∧
        ∃ k : ℕ, ∃ _chain : CactusFoldChain Delta Next k,
          Next.innerFaceCount + k = Delta.innerFaceCount ∧
          Delta.boundaryWord =
            (List.replicate n (word.map signedFreeRelLetter)).flatten

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- Strong induction over the exact area index turns a cactus fold chain into
the retyped relator-only disc required by the torsion extraction. -/
theorem cactusRelatorRetypingForPower_of_foldChainSource
    (hsource : CactusPowerFoldChainSource (T := T)) :
    CactusRelatorRetypingForPower T := by
  rw [CactusPowerFoldChainSource] at hsource
  intro g n hn hpow hne word hword
  obtain ⟨Delta, Next, hplanar, hred, k, chain, _harea, hboundary⟩ :=
    hsource g n hn hpow hne word hword
  let R : CactusRelatorRetyping Delta :=
    chain.toRetyping hplanar hred
  refine ⟨Delta, R, ?_⟩
  have hterminal : Next.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten :=
    chain.terminal_boundaryWord_eq
      (word.map signedFreeRelLetter) n hboundary
  have hsame : R.diagram = Next :=
    chain.toRetyping_diagram_eq hplanar hred
  rw [hsame]
  exact hterminal

/-! A one-cell model test records the exact drop, rather than weakening it
   to an inequality. -/
omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
theorem cactusPowerFoldStep_oneCell_model
    {Delta : DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (C : CactusBaseCellFoldData Delta)
    (hone : Delta.innerFaceCount = 1) :
    C.replacement.diagram.innerFaceCount = 0 := by
  exact C.area_zero_of_oneCell hone

/-! ## Exposed pairing and Euler counts -/

/-- `girthDegree`/`hgeom` were added because `ExposedPairingEulerInput.pairUnique
: TrianglePairUnique T` had no source anywhere in the original statement --
the repository's only route to `TrianglePairUnique T` is
`trianglePairUnique_of_girthEightChecks`, which needs `GirthEightChecks T d`
for some `d`. The consumer (`sharpExistence_of_checkedTable`, which quantifies
this producer) already has such a hypothesis in scope at its call site, so
this costs it nothing; it is the honest hypothesis this producer's conclusion
needs, not a strengthening chosen for convenience. -/
def PlanarDiscExposedPairingEulerProducer : Type 1 :=
  ∀ (Generator TriangleIndex : Type)
    (_ : Fintype Generator) (_ : DecidableEq Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → Triangle Generator)
    (girthDegree : ℕ) (_ : GirthEightChecks T girthDegree)
    (g : Presented T) (n : ℕ) (D : PowerDisc T g n),
    ExposedPairingEulerInput T D

/-- Raw seam geometry for the exposed-pairing producer.  The mate is built
from a boundary indexing equivalence, connectedness is supplied by a landed
path certificate, and the three finite incidence equivalences are the
vertex/edge/face count calculation for the seam quotient. -/
structure PlanarDiscExposedPairingGeometry
    (T : TriangleIndex → Triangle Generator)
    {g : Presented T} {n : ℕ}
    (D : PowerDisc T g n) where
  indexType : Type
  index : ExposedCopiedDart D.diagram n ≃ Fin n × indexType
  index_copy : ∀ d, (index d).1 = d.1.1
  copyMate : Equiv.Perm (Fin n)
  hinvol : Function.Involutive copyMate
  hfree : ∀ i, copyMate i ≠ i
  connected : (ExposedPairing.of_copyMate index index_copy copyMate hinvol hfree).toPairing.closedMap.IsConnected
  incidence : Pairing.EulerTwoCountData
    (ExposedPairing.of_copyMate index index_copy copyMate hinvol hfree).toPairing
  corner : ∀ v, VertexCornerCertificate T
    (cornerCycleOfCombMap
      (ExposedPairing.of_copyMate index index_copy copyMate hinvol hfree).toPairing.closedMap v)
  cellular : ∀ v, CellularReducedAt (corner v)

/-- The raw seam geometry supplies exactly the existential package named
`PlanarDiscExposedPairingEulerData`.  The exposed mate is the concrete
quotient pairing, and the incidence equations are passed through unchanged
to the landed `EulerTwoCountData` record; `pairUnique` is read off the
producer's own `GirthEightChecks` hypothesis via
`trianglePairUnique_of_girthEightChecks`. -/
noncomputable def planarDiscExposedPairingEulerData_of_planarDisc
    (hsource : ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → Triangle Generator)
      (g : Presented T) (n : ℕ) (D : PowerDisc T g n),
      PlanarDiscExposedPairingGeometry T D) :
    PlanarDiscExposedPairingEulerProducer := by
  intro Generator TriangleIndex fg dg ft dt T girthDegree hgeom g n D
  let G := hsource Generator TriangleIndex fg dg ft dt T g n D
  exact
    { pairing := ExposedPairing.of_copyMate G.index G.index_copy G.copyMate G.hinvol G.hfree
      pairUnique := trianglePairUnique_of_girthEightChecks hgeom
      counts := G.incidence
      corner := G.corner
      cellular := G.cellular }

/-! ## A named missing producer, not a proof gap

`doubleEulerCountData_of_incidence` and `planarDiscGeometry_of_double` are
**not present in this file.**  Both were attempted and removed: they target a
producer that does not exist, and no supply of hypotheses could ever have
completed them.  This is recorded here rather than left as a broken `theorem`
because the two facts below settle the question, not just the tactic:

**`ExposedPairingEulerInput.counts` was never the problem.**
`KazhdanHypGirthEightTorsionExtraction.lean:488` calls
`powerDiscSphereGluing_of_eulerCounts hD hinput.pairing.toPairing hinput.counts
...` directly, at *arbitrary* `n`; `KazhdanHypGirthEightPrimitives2.lean:1021`
and `:1050` (`powerDiscSphereGluing_of_eulerCounts`,
`powerDiscSphereGluing_of_planarDisc`) both take `Pairing.EulerTwoCountData`
for general `n`. `EulerTwoCountData`'s formula gives `χ_S = n·2 - 2n + 2 = 2`
for every `n` -- exactly the connected-sphere invariant the cyclic
construction needs. So `ExposedPairingEulerInput.counts : EulerTwoCountData`
is correctly typed and needs no change.

**The construction this file had for it targets a different, already-served
consumer instead.** `KazhdanHypSharpExistenceAssembly.lean:67-68` says, of the
seam this producer is for:

    `H.seam` supplies `ExposedPairingEulerInput` for that same arbitrary `n`;
    ...
    The cyclic gluing is a sphere from copies of that disc.

`ExposedPairing.of_copyMate`/`of_doubleCopyMate`, which `planarDiscGeometry_of_
double` built its geometry from, do not construct a cyclic gluing: `copyMate`
is required to be a fixed-point-free involution on `Fin n`, so it pairs the
`n` copies into `n / 2` *disjoint* pairs, each glued along its own full shared
boundary independently of every other pair. At general `n` that produces
`n / 2` disjoint spheres (Euler characteristic `n`, checked directly), not one
connected sphere -- so no proof from this seam could ever reach `EulerTwoCount
Data`, whose sole content beyond planarity IS connectedness plus `χ = 2`. And
this was never going to close even at `n = 2`: `of_doubleCopyMate`'s own
whole-boundary count (`DoubleEulerCountData`, `vertexCount_S + boundary = 2 *
vertexCount_Δ`) agrees with `EulerTwoCountData`'s two-seam-vertex count
(`vertexCount_S = 2 * vertexCount_Δ` at `n = 2`) only when `boundary = 0`,
which is false for any disc with a nonempty boundary. The near-matching types
hid a construction aimed at a different entry point:
`powerDiscSphereGluing_of_doubleCopyMate` (`Primitives2.lean:1059`), the
already-working `n = 2`, disjoint-involution-seam route that `of_doubleCopyMate`
and `DoubleEulerCountData` correctly serve, and were presumably built for.

**What is actually missing:** a producer of `ExposedPairing`/`Pairing` at
general `n` whose counts satisfy `EulerTwoCountData` -- realizing the cyclic
gluing the assembly's own docstring describes. Nothing in the repository
builds one. That is new geometry (the rotational/cyclic seam construction
itself), not a retype and not a tactic gap, and it is not attempted here. -/

end GGT
end GroupApproximation
