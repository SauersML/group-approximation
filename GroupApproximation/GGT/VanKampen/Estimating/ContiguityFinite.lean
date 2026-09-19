import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Data.Fintype.List
import GroupApproximation.Meta.AxiomGuard

/-!
# Finitely many actual embedded contiguities in a fixed disc

The code retains the boundary cycle, carrier indices, arc starts and lengths,
and both side lists. Every side is a sublist of the duplicate-free boundary.
All other fields of a contiguity are proofs. This gives a finite optimization
domain without discarding a witness whose arc weight must be compared.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

theorem FaceSetBoundary.eq_of_cycle_eq {B K : FaceSetBoundary Delta faces}
    (h : B.cycle = K.cycle) : B = K := by
  cases B
  cases K
  cases h
  rfl

theorem CyclicArc.eq_of_start_length {A : Type v} {cycle : List A}
    {a b : CyclicArc cycle} (hs : a.start.val = b.start.val) (hl : a.length = b.length) : a = b := by
  cases a
  cases b
  have hstart := Fin.ext hs
  cases hstart
  cases hl
  rfl

namespace Contiguity

theorem eq_of_data {H K : Contiguity D eps Delta faces}
    (hb : H.boundary.cycle = K.boundary.cycle)
    (hs : H.source = K.source) (ht : H.target = K.target)
    (hss : H.sourceArc.start.val = K.sourceArc.start.val)
    (hsl : H.sourceArc.length = K.sourceArc.length)
    (hts : H.targetArc.start.val = K.targetArc.start.val)
    (htl : H.targetArc.length = K.targetArc.length)
    (hr : H.rightSide = K.rightSide) (hl : H.leftSide = K.leftSide) : H = K := by
  cases H
  cases K
  cases hs
  cases ht
  have hboundary := FaceSetBoundary.eq_of_cycle_eq hb
  have hsource := CyclicArc.eq_of_start_length hss hsl
  have htarget := CyclicArc.eq_of_start_length hts htl
  cases hboundary
  cases hsource
  cases htarget
  cases hr
  cases hl
  rfl

theorem rightSide_nodup (H : Contiguity D eps Delta faces) : H.rightSide.Nodup := by
  have h := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at h
  have habc := (List.nodup_append.mp h).1
  have hab := (List.nodup_append.mp habc).1
  exact (List.nodup_append.mp hab).2.1

theorem leftSide_nodup (H : Contiguity D eps Delta faces) : H.leftSide.Nodup := by
  have h := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at h
  exact (List.nodup_append.mp h).2.1

def FiniteCode (Delta : DiscDiagram.{u, w, v} W) :=
  { l : List Delta.toCombMap.Dart // l.Nodup } ×
    (Σ i : Fin Delta.rCellCount,
      Fin ((cellDarts Delta i).length + 1) × Fin ((cellDarts Delta i).length + 1)) ×
    (Σ i : Option (Fin Delta.rCellCount),
      Fin ((targetDarts Delta i).length + 1) × Fin ((targetDarts Delta i).length + 1)) ×
    { l : List Delta.toCombMap.Dart // l.Nodup } ×
    { l : List Delta.toCombMap.Dart // l.Nodup }

noncomputable instance finiteCodeFintype : Fintype (FiniteCode Delta) := by
  classical
  unfold FiniteCode
  infer_instance

def finiteCode (H : Contiguity D eps Delta faces) : FiniteCode Delta :=
  ⟨⟨H.boundary.cycle, H.boundary.cycle_nodup⟩,
    ⟨H.source, H.sourceArc.start, ⟨H.sourceArc.length, Nat.lt_succ_iff.mpr H.sourceArc.length_le⟩⟩,
    ⟨H.target, H.targetArc.start, ⟨H.targetArc.length, Nat.lt_succ_iff.mpr H.targetArc.length_le⟩⟩,
    ⟨H.rightSide, H.rightSide_nodup⟩, ⟨H.leftSide, H.leftSide_nodup⟩⟩

theorem finiteCode_injective : Function.Injective (finiteCode : Contiguity D eps Delta faces → _) := by
  intro H K h
  have hb : H.boundary.cycle = K.boundary.cycle := congrArg (fun x => x.1.val) h
  have hs : H.source = K.source := congrArg (fun x => x.2.1.1) h
  have ht : H.target = K.target := congrArg (fun x => x.2.2.1.1) h
  have hss : H.sourceArc.start.val = K.sourceArc.start.val :=
    congrArg (fun x => x.2.1.2.1.val) h
  have hsl : H.sourceArc.length = K.sourceArc.length :=
    congrArg (fun x => x.2.1.2.2.val) h
  have hts : H.targetArc.start.val = K.targetArc.start.val :=
    congrArg (fun x => x.2.2.1.2.1.val) h
  have htl : H.targetArc.length = K.targetArc.length :=
    congrArg (fun x => x.2.2.1.2.2.val) h
  have hr : H.rightSide = K.rightSide := congrArg (fun x => x.2.2.2.1.val) h
  have hl : H.leftSide = K.leftSide := congrArg (fun x => x.2.2.2.2.val) h
  exact eq_of_data hb hs ht hss hsl hts htl hr hl

noncomputable instance contiguityFintype : Fintype (Contiguity D eps Delta faces) := by
  classical
  exact Fintype.ofInjective finiteCode finiteCode_injective

end Contiguity
end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.finiteCode_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.Contiguity.contiguityFintype
