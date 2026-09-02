import GroupApproximation.GGT.KazhdanHypSharpExistenceAssembly
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
open VanKampen
open VanKampen.SeamGluing
open GirthEightTorsionExtraction

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
          C.before_power =
              (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
          C.after_power =
              (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
          C.replacement.diagram.innerFaceCount + 1 =
              Delta.innerFaceCount

/-- The landed fold data is a concrete constructor for the exact
`CactusBaseCellDeletionForPower` producer.  The first two conclusions are
the unchanged boundary power and the last is the exact one-cell area drop. -/
theorem cactusBaseCellDeletionForPower_of_foldStepSource
    (hsource : CactusPowerFoldStepSource (T := T)) :
    CactusBaseCellDeletionForPower T := by
  intro g n hn hpow hne word hword
  obtain ⟨Delta, hplanar, C, hbefore, hafter, hdrop⟩ :=
    hsource g n hn hpow hne word hword
  refine ⟨Delta, hplanar, C.toDeletion, ?_⟩
  exact hafter

/-- A power-fold chain source.  Each step is a concrete landed
`CactusBaseCellDeletion`; the chain index is the number of deleted base
cells, so induction on it gives the strong area induction used in the
cactus argument. -/
def CactusPowerFoldChainSource : Prop :=
  ∀ (g : Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 →
    ∀ (word : List (SignedGenerator Generator)),
      PresentedGroup.mk (relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      ∃ Delta Next : DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.toCombMap.IsPlanar ∧ Delta.Reduced ∧
        ∃ k : ℕ, ∃ chain : CactusFoldChain Delta Next k,
          Delta.boundaryWord =
            (List.replicate n (word.map signedFreeRelLetter)).flatten

/-- Strong induction over the exact area index turns a cactus fold chain into
the retyped relator-only disc required by the torsion extraction. -/
theorem cactusRelatorRetypingForPower_of_foldChainSource
    (hsource : CactusPowerFoldChainSource (T := T)) :
    CactusRelatorRetypingForPower T := by
  intro g n hn hpow hne word hword
  obtain ⟨Delta, Next, hplanar, hred, k, chain, hboundary⟩ :=
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
theorem cactusPowerFoldStep_oneCell_model
    {Delta : DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (C : CactusBaseCellFoldData Delta)
    (hone : Delta.innerFaceCount = 1) :
    C.replacement.diagram.innerFaceCount = 0 := by
  exact C.area_zero_of_oneCell hone

/-! ## Exposed pairing and Euler counts -/

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
to the landed `EulerTwoCountData` record. -/
theorem planarDiscExposedPairingEulerData_of_planarDisc
    (hsource : ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → Triangle Generator)
      (g : Presented T) (n : ℕ) (D : PowerDisc T g n),
      PlanarDiscExposedPairingGeometry T D) :
    PlanarDiscExposedPairingEulerData := by
  intro Generator TriangleIndex fg dg ft dt T g n D
  let G := hsource Generator TriangleIndex fg dg ft dt T g n D
  let B := ExposedPairing.of_copyMate G.index G.index_copy G.copyMate
    G.hinvol G.hfree
  refine ⟨G.indexType, G.index, G.index_copy, G.copyMate,
    G.hinvol, G.hfree, ?_, G.corner, G.cellular⟩
  exact G.incidence

/-- In the double model, the incidence maps from `DoubleIncidenceEquivalences`
produce the count package consumed by the generic seam theorem. -/
theorem doubleEulerCountData_of_incidence
    {g : Presented T} {D : PowerDisc T g 2}
    {B : ExposedPairing D.diagram 2}
    (C : DoubleIncidenceEquivalences B.toPairing)
    (K : DoubleConnectivityData B.toPairing) :
    Pairing.EulerTwoCountData B.toPairing := by
  have hD := C.toEulerCountData K
  refine {
    connected := connected_of_doubleConnectivityData K
    vertex_count_eq := ?_
    edge_count_eq := ?_
    face_count_eq := ?_ }
  · have hv := hD.vertex_count_eq
    omega
  · have he := hD.edge_count_eq
    omega
  · have hf := hD.face_count_eq
    omega

end GGT
end GroupApproximation
