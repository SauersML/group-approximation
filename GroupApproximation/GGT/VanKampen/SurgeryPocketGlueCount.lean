import GroupApproximation.GGT.VanKampen.SurgeryPocketGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# Darts, edges and faces of the glued map

Let `S` be seam data between a face set `faces` of `M` and a face `outer` of `X`, and let
`piece` be `M` with the edges internal to `faces` deleted and the region reclosed.  The glued
map and `piece` together have as many darts, edges and faces as `M` and `X` together:

* the glued darts are the darts of `M` on `faces` and the darts of `X` off `outer`, while the
  darts of `piece` are the darts of `M` off `faces` and the boundary darts of `faces`, which
  correspond to the darts of `outer`;
* the glued faces are the faces in `faces` and the faces of `X` other than `outer`, while
  `piece` has the faces of `M` outside `faces` and one new face.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

open Equiv MapCollapse

universe v

/-- A predicate splits the cardinality of a finite type. -/
theorem card_sum_compl {α : Type v} [Finite α] (p : α → Prop) :
    Nat.card {a : α // p a} + Nat.card {a : α // ¬p a} = Nat.card α := by
  classical
  have h : Nat.card ({a : α // p a} ⊕ {a : α // ¬p a}) = Nat.card α :=
    Nat.card_congr (Equiv.sumCompl p)
  rw [Nat.card_sum] at h
  exact h

private def orbitSubtypeToFun {D : Type v} (f : Perm D) (T : CombMap.Orbit f → Prop)
    (hT : ∀ d, T (Quotient.mk'' (f d)) ↔ T (Quotient.mk'' d)) :
    CombMap.Orbit (f.subtypePerm (p := fun d => T (Quotient.mk'' d)) hT) →
      {c : CombMap.Orbit f // T c} :=
  Quotient.lift (fun d => (⟨Quotient.mk'' d.1, d.2⟩ : {c : CombMap.Orbit f // T c}))
    (fun x y hxy => by
      apply Subtype.ext
      have hsame : Equiv.Perm.SameCycle
          (f.subtypePerm (p := fun d => T (Quotient.mk'' d)) hT) x y := hxy
      exact Quotient.sound
        ((sameCycle_subtypePerm f (P := fun d => T (Quotient.mk'' d)) hT x y).1 hsame))

private theorem orbitSubtypeToFun_injective {D : Type v} (f : Perm D)
    (T : CombMap.Orbit f → Prop) (hT : ∀ d, T (Quotient.mk'' (f d)) ↔ T (Quotient.mk'' d)) :
    Function.Injective (orbitSubtypeToFun f T hT) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y hxy
  apply Quotient.sound
  have hval : (Quotient.mk'' x.1 : CombMap.Orbit f) = Quotient.mk'' y.1 :=
    congrArg (fun z : {c : CombMap.Orbit f // T c} => z.1) hxy
  have hsame : Equiv.Perm.SameCycle f x.1 y.1 := Quotient.exact hval
  show Equiv.Perm.SameCycle (f.subtypePerm (p := fun d => T (Quotient.mk'' d)) hT) x y
  exact (sameCycle_subtypePerm f (P := fun d => T (Quotient.mk'' d)) hT x y).2 hsame

private theorem orbitSubtypeToFun_surjective {D : Type v} (f : Perm D)
    (T : CombMap.Orbit f → Prop) (hT : ∀ d, T (Quotient.mk'' (f d)) ↔ T (Quotient.mk'' d)) :
    Function.Surjective (orbitSubtypeToFun f T hT) := by
  intro p
  obtain ⟨c, hc⟩ := p
  revert hc
  refine Quotient.inductionOn c ?_
  intro d hd
  exact ⟨Quotient.mk'' ⟨d, hd⟩, rfl⟩

/-- The orbits of a permutation restricted to the points of an invariant set of orbits are
those orbits. -/
def orbitSubtypeEquiv {D : Type v} (f : Perm D) (T : CombMap.Orbit f → Prop)
    (hT : ∀ d, T (Quotient.mk'' (f d)) ↔ T (Quotient.mk'' d)) :
    CombMap.Orbit (f.subtypePerm (p := fun d => T (Quotient.mk'' d)) hT) ≃
      {c : CombMap.Orbit f // T c} :=
  Equiv.ofBijective (orbitSubtypeToFun f T hT)
    ⟨orbitSubtypeToFun_injective f T hT, orbitSubtypeToFun_surjective f T hT⟩

namespace Seam

variable {M X : CombMap.{v}} (S : Seam M X)

/-- The reclosed pocket: `M` with the edges internal to `faces` deleted. -/
abbrev piece : CombMap.{v} := reclosedMap M S.faces S.boundary

theorem glue_dartCount :
    S.glueMap.dartCount + S.piece.dartCount = M.dartCount + X.dartCount := by
  classical
  have hglue : S.glueMap.dartCount =
      Nat.card {d : M.Dart // M.faceOf d ∈ S.faces} +
        Nat.card {x : X.Dart // X.faceOf x ≠ S.outer} := by
    change Nat.card S.GlueDart = _
    exact Nat.card_sum
  have hpiece : S.piece.dartCount =
      Nat.card (OutsideDart M S.faces) + Nat.card (BoundaryDart M S.faces) := by
    have h : Nat.card (KeptDart M S.faces) =
        Nat.card (OutsideDart M S.faces ⊕ BoundaryDart M S.faces) :=
      Nat.card_congr (keptSplitEquiv M S.faces)
    rw [Nat.card_sum] at h
    exact h
  have hM : Nat.card {d : M.Dart // M.faceOf d ∈ S.faces} +
      Nat.card (OutsideDart M S.faces) = M.dartCount :=
    card_sum_compl (fun d : M.Dart => M.faceOf d ∈ S.faces)
  have hX : Nat.card {x : X.Dart // X.faceOf x = S.outer} +
      Nat.card {x : X.Dart // X.faceOf x ≠ S.outer} = X.dartCount :=
    card_sum_compl (fun x : X.Dart => X.faceOf x = S.outer)
  have hseam : Nat.card (BoundaryDart M S.faces) =
      Nat.card {x : X.Dart // X.faceOf x = S.outer} :=
    Nat.card_congr S.seamEquiv
  omega

theorem glue_edgeCount :
    S.glueMap.edgeCount + S.piece.edgeCount = M.edgeCount + X.edgeCount := by
  have h := S.glue_dartCount
  have h1 := S.glueMap.dartCount_eq_two_mul_edgeCount
  have h2 := S.piece.dartCount_eq_two_mul_edgeCount
  have h3 := M.dartCount_eq_two_mul_edgeCount
  have h4 := X.dartCount_eq_two_mul_edgeCount
  omega

/-- Faces of the glued map: the faces in `faces` and the faces of `X` other than `outer`. -/
def glueFaceEquiv :
    S.glueMap.Face ≃ {f : M.Face // f ∈ S.faces} ⊕ {f : X.Face // f ≠ S.outer} :=
  (orbitCongrOfEq S.glueMap_facePerm).trans
    ((orbitSumCongr
        (M.facePerm.subtypePerm (p := fun d => M.faceOf d ∈ S.faces)
          (fun d => iff_of_eq (congrArg (· ∈ S.faces) (M.faceOf_facePerm d))))
        (X.facePerm.subtypePerm (p := fun x => X.faceOf x ≠ S.outer)
          (fun x => iff_of_eq (congrArg (· ≠ S.outer) (X.faceOf_facePerm x))))).trans
      (Equiv.sumCongr
        (orbitSubtypeEquiv M.facePerm (fun f => f ∈ S.faces)
          (fun d => iff_of_eq (congrArg (· ∈ S.faces) (M.faceOf_facePerm d))))
        (orbitSubtypeEquiv X.facePerm (fun f => f ≠ S.outer)
          (fun x => iff_of_eq (congrArg (· ≠ S.outer) (X.faceOf_facePerm x))))))

theorem glue_faceCount :
    S.glueMap.faceCount + S.piece.faceCount = M.faceCount + X.faceCount := by
  classical
  have hglue : S.glueMap.faceCount =
      Nat.card {f : M.Face // f ∈ S.faces} + Nat.card {f : X.Face // f ≠ S.outer} := by
    have h : Nat.card S.glueMap.Face =
        Nat.card ({f : M.Face // f ∈ S.faces} ⊕ {f : X.Face // f ≠ S.outer}) :=
      Nat.card_congr S.glueFaceEquiv
    rw [Nat.card_sum] at h
    exact h
  have hmem : Nat.card {f : M.Face // f ∈ S.faces} = S.faces.card :=
    Nat.card_eq_finsetCard S.faces
  have hpiece : S.piece.faceCount + S.faces.card = M.faceCount + 1 :=
    reclosedMap_faceCount M S.faces S.boundary
  have hX : Nat.card {f : X.Face // f = S.outer} + Nat.card {f : X.Face // f ≠ S.outer} =
      X.faceCount :=
    card_sum_compl (fun f : X.Face => f = S.outer)
  have hunit : Nat.card {f : X.Face // f = S.outer} = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨S.outer, rfl⟩⟩⟩
  omega

end Seam

end GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.orbitSubtypeEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_edgeCount
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_faceCount
