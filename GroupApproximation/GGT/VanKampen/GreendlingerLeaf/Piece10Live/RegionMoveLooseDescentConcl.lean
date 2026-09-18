import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveCoreClose
import GroupApproximation.Meta.AxiomGuard

/-!
# The conclusion of the core depends only on the faces

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-24.

## Route

* `RegionMoveLooseDescentConcl K`: the conclusion of `RegionMoveCoreCloseStatement` for the pocket
  `K`, word for word.
* `regionMoveLooseDescent_cycle_perm` (proved): two pockets with the same faces list the same
  boundary darts, so their boundary cycles are permutations of each other.
* `regionMoveLooseDescent_concl_of_faces_eq` (proved): the conclusion passes between two pockets
  with the same faces.  It reads the boundary cycle only through the edge predicate
  `walkKeep` (membership) and through a filter taken up to permutation.

So a surgery that only reorders the boundary walk of a pocket, keeping its faces, always transfers
the conclusion back.

## Status

Everything here is proved.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The conclusion of the core for one pocket**: the conclusion of
`RegionMoveCoreCloseStatement`, word for word. -/
def RegionMoveLooseDescentConcl (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ r : X.toCombMap.Dart,
    (∀ x, X.toCombMap.faceOf x = X.outerFace → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) r x) ∧
    ∃ (source kept : Fin X.rCellCount),
      (cell X source).face ∉ flipFaces X.toCombMap K.faces
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
      (cell X kept).face ∈ flipFaces X.toCombMap K.faces
        (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r) ∧
      ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
        (s₁ s₂ : List X.toCombMap.Dart),
        List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
          (K.boundary.cycle.filter (movePred X.toCombMap
            (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) r))) ∧
        s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts ≠ [] ∧
        (s₁.IsChain fun d e =>
          X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
        (s₂.IsChain fun d e =>
          X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
        (∀ a ∈ s₁.getLast?, ∀ b ∈ (invDarts X t₁.darts).head?,
          X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
        (∀ a ∈ (s₁ ++ invDarts X t₁.darts).getLast?, ∀ b ∈ s₂.head?,
          X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
        (∀ a ∈ (s₁ ++ invDarts X t₁.darts ++ s₂).getLast?, ∀ b ∈ t₂.darts.head?,
          X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
        t₂.start.1 + t₂.length ≤ hi ∧
        t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

/-- **Pockets with the same faces have permuted boundary cycles.** -/
theorem regionMoveLooseDescent_cycle_perm {K K' : PocketFaceSet D eps X lo hi}
    (hf : K.faces = K'.faces) : K.boundary.cycle.Perm K'.boundary.cycle := by
  rw [List.perm_ext_iff_of_nodup K.boundary.cycle_nodup K'.boundary.cycle_nodup]
  intro d
  rw [K.boundary.cycle_mem_iff, K'.boundary.cycle_mem_iff, hf]

/-- **The conclusion passes between pockets with the same faces.** -/
theorem regionMoveLooseDescent_concl_of_faces_eq {K K' : PocketFaceSet D eps X lo hi}
    (hf : K.faces = K'.faces) (h : RegionMoveLooseDescentConcl K) :
    RegionMoveLooseDescentConcl K' := by
  have hperm := regionMoveLooseDescent_cycle_perm hf
  have hk : walkKeep X.toCombMap K.boundary.cycle = walkKeep X.toCombMap K'.boundary.cycle := by
    funext d
    simp only [walkKeep, hperm.mem_iff]
  have hff : ∀ z, flipFaces X.toCombMap K.faces z = flipFaces X.toCombMap K'.faces z := by
    intro z
    rw [hf]
  obtain ⟨r, hr, source, kept, hs, hkp, t₁, t₂, s₁, s₂, hp, hrest⟩ := h
  refine ⟨r, ?_, source, kept, ?_, ?_, t₁, t₂, s₁, s₂, ?_, hrest⟩
  · rw [← hk]
    exact hr
  · rw [← hk, ← hff]
    exact hs
  · rw [← hk, ← hff]
    exact hkp
  · rw [← hk]
    exact hp.trans (List.Perm.filter _ hperm)

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseDescentConcl
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_cycle_perm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_concl_of_faces_eq
