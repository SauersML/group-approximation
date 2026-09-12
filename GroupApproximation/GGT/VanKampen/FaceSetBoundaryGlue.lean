import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Gluing two face-set boundaries along one arc

Let `F₁` and `F₂` be disjoint sets of G-cells with single boundary cycles, meeting along one
arc: the cycle of `F₁` reads `P ++ S`, the cycle of `F₂` reads the reverse of `S` followed by
`Q`, and every edge from a face of `F₁` to a face of `F₂` lies on `S`.  Then `F₁ ∪ F₂` has the
single boundary cycle `P ++ Q`.  This is the gluing step in the proof of Osin's Lemma 9.7(b)
(arXiv:math/0411039v3), where two regions of the distinguished system from one cell to one
section and the pocket between them form one region.

The proof traces the boundary.  A dart of `P` or of `Q` still has a face of the union on its
left and none on its right, because `F₁` meets `F₂` only along `S`.  A boundary step of either
cycle is a step of the union, since an internal move of a subset is an internal move of the
union.  At each of the two junctions the tracing reaches `S`, crosses to its reverse by one
more internal move, and continues along the other cycle.

## What is proved here

* `internalBoundaryMove_of_subset` and `reflTransGen_internalBoundaryMove_of_subset`: internal
  moves are monotone in the face set;
* `FaceSetBoundary.glue_isBoundaryDart_left`, `FaceSetBoundary.glue_isBoundaryDart_right` and
  `FaceSetBoundary.glue_mem_of_isBoundaryDart`: the boundary darts of the union are exactly
  the darts of `P ++ Q`;
* `FaceSetBoundary.glue`: the boundary cycle `P ++ Q` of `F₁ ∪ F₂`, for nonempty `P`, `S`
  and `Q`, with `FaceSetBoundary.glue_cycle`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-! ## List bookkeeping -/

theorem glue_eq_head_of_mem_head? {α : Type*} {l : List α} (hne : l ≠ [])
    {d : α} (hd : d ∈ l.head?) : d = l.head hne := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a tail =>
      have hmem : a = d := by
        simpa only [List.head?, Option.mem_def, Option.some_inj] using hd
      exact hmem.symm

theorem glue_head_congr {α : Type*} {left right : List α}
    (hleft : left ≠ []) (hright : right ≠ []) (heq : left = right) :
    left.head hleft = right.head hright := by
  subst right
  rfl

/-! ## Internal moves of a larger face set -/

/-- An internal move of a face set is an internal move of every larger face set. -/
theorem internalBoundaryMove_of_subset {F F' : Finset Delta.toCombMap.Face} (hsub : F ⊆ F')
    {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta F d e) :
    InternalBoundaryMove Delta F' d e :=
  ⟨hsub h.1, hsub h.2.1, h.2.2⟩

/-- A run of internal moves of a face set is a run of internal moves of every larger face
set. -/
theorem reflTransGen_internalBoundaryMove_of_subset {F F' : Finset Delta.toCombMap.Face}
    (hsub : F ⊆ F') {d e : Delta.toCombMap.Dart}
    (h : Relation.ReflTransGen (InternalBoundaryMove Delta F) d e) :
    Relation.ReflTransGen (InternalBoundaryMove Delta F') d e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih (internalBoundaryMove_of_subset hsub hstep)

section Glue

variable [DecidableEq Delta.toCombMap.Face]

/-! ## The boundary darts of the union -/

/-- A dart of `P` is a boundary dart of the union: its right face is not in `F₂`, since an
edge from `F₁` to `F₂` lies on `S`. -/
theorem FaceSetBoundary.glue_isBoundaryDart_left {F₁ F₂ : Finset Delta.toCombMap.Face}
    (B₁ : FaceSetBoundary Delta F₁) {P S : List Delta.toCombMap.Dart}
    (h₁ : B₁.cycle = P ++ S)
    (hadj : ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d ∈ F₁ →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ F₂ → d ∈ S)
    {d : Delta.toCombMap.Dart} (hd : d ∈ P) :
    IsBoundaryDart Delta (F₁ ∪ F₂) d := by
  have hcyc : d ∈ B₁.cycle := by
    rw [h₁]
    exact List.mem_append_left S hd
  obtain ⟨hin, hout⟩ := (B₁.cycle_mem_iff d).mp hcyc
  refine ⟨Finset.mem_union_left F₂ hin, ?_⟩
  intro hunion
  rcases Finset.mem_union.mp hunion with h | h
  · exact hout h
  · have hnodup : (P ++ S).Nodup := by
      rw [← h₁]
      exact B₁.cycle_nodup
    exact (List.nodup_append.mp hnodup).2.2 d hd d (hadj d hin h) rfl

/-- A dart of `Q` is a boundary dart of the union: its right face is not in `F₁`, since the
reverse of an edge from `F₁` to `F₂` lies on `S`. -/
theorem FaceSetBoundary.glue_isBoundaryDart_right {F₁ F₂ : Finset Delta.toCombMap.Face}
    (B₂ : FaceSetBoundary Delta F₂) {S Q : List Delta.toCombMap.Dart}
    (h₂ : B₂.cycle = S.reverse.map Delta.toCombMap.alpha ++ Q)
    (hadj : ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d ∈ F₁ →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ F₂ → d ∈ S)
    {d : Delta.toCombMap.Dart} (hd : d ∈ Q) :
    IsBoundaryDart Delta (F₁ ∪ F₂) d := by
  have hcyc : d ∈ B₂.cycle := by
    rw [h₂]
    exact List.mem_append_right _ hd
  obtain ⟨hin, hout⟩ := (B₂.cycle_mem_iff d).mp hcyc
  refine ⟨Finset.mem_union_right F₁ hin, ?_⟩
  intro hunion
  rcases Finset.mem_union.mp hunion with h | h
  · have hS : Delta.toCombMap.alpha d ∈ S := by
      apply hadj (Delta.toCombMap.alpha d) h
      rw [Delta.toCombMap.alpha_involutive d]
      exact hin
    have hmem : d ∈ S.reverse.map Delta.toCombMap.alpha := by
      rw [List.mem_map]
      exact ⟨Delta.toCombMap.alpha d, List.mem_reverse.mpr hS,
        Delta.toCombMap.alpha_involutive d⟩
    have hnodup : (S.reverse.map Delta.toCombMap.alpha ++ Q).Nodup := by
      rw [← h₂]
      exact B₂.cycle_nodup
    exact (List.nodup_append.mp hnodup).2.2 d hmem d hd rfl
  · exact hout h

/-- A boundary dart of the union lies on `P ++ Q`: a boundary dart of `F₁` on `S` faces `F₂`,
and a boundary dart of `F₂` on the reverse of `S` faces `F₁`. -/
theorem FaceSetBoundary.glue_mem_of_isBoundaryDart {F₁ F₂ : Finset Delta.toCombMap.Face}
    (B₁ : FaceSetBoundary Delta F₁) (B₂ : FaceSetBoundary Delta F₂)
    {P S Q : List Delta.toCombMap.Dart}
    (h₁ : B₁.cycle = P ++ S) (h₂ : B₂.cycle = S.reverse.map Delta.toCombMap.alpha ++ Q)
    {d : Delta.toCombMap.Dart} (hd : IsBoundaryDart Delta (F₁ ∪ F₂) d) :
    d ∈ P ++ Q := by
  obtain ⟨hin, hout⟩ := hd
  rcases Finset.mem_union.mp hin with h | h
  · have hcyc : d ∈ B₁.cycle :=
      (B₁.cycle_mem_iff d).mpr ⟨h, fun h' => hout (Finset.mem_union_left F₂ h')⟩
    rw [h₁] at hcyc
    rcases List.mem_append.mp hcyc with hP | hS
    · exact List.mem_append_left Q hP
    · exfalso
      have hmem : Delta.toCombMap.alpha d ∈ B₂.cycle := by
        rw [h₂]
        apply List.mem_append_left
        rw [List.mem_map]
        exact ⟨d, List.mem_reverse.mpr hS, rfl⟩
      exact hout (Finset.mem_union_right F₁ ((B₂.cycle_mem_iff _).mp hmem).1)
  · have hcyc : d ∈ B₂.cycle :=
      (B₂.cycle_mem_iff d).mpr ⟨h, fun h' => hout (Finset.mem_union_right F₁ h')⟩
    rw [h₂] at hcyc
    rcases List.mem_append.mp hcyc with hS | hQ
    · exfalso
      rw [List.mem_map] at hS
      obtain ⟨e, he, rfl⟩ := hS
      have hmem : e ∈ B₁.cycle := by
        rw [h₁]
        exact List.mem_append_right P (List.mem_reverse.mp he)
      apply hout
      rw [Delta.toCombMap.alpha_involutive e]
      exact Finset.mem_union_left F₂ ((B₁.cycle_mem_iff e).mp hmem).1
    · exact List.mem_append_right P hQ

/-! ## The glued boundary -/

/-- **Gluing two boundaries along one arc.**  If the cycle of `F₁` is `P ++ S`, the cycle of
`F₂` is the reverse of `S` followed by `Q`, the face sets are disjoint and every edge from
`F₁` to `F₂` lies on `S`, then `P ++ Q` is the boundary cycle of `F₁ ∪ F₂`. -/
def FaceSetBoundary.glue {F₁ F₂ : Finset Delta.toCombMap.Face}
    (B₁ : FaceSetBoundary Delta F₁) (B₂ : FaceSetBoundary Delta F₂)
    (hdisj : Disjoint F₁ F₂) {P S Q : List Delta.toCombMap.Dart}
    (hP : P ≠ []) (hS : S ≠ []) (hQ : Q ≠ [])
    (h₁ : B₁.cycle = P ++ S) (h₂ : B₂.cycle = S.reverse.map Delta.toCombMap.alpha ++ Q)
    (hadj : ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d ∈ F₁ →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ F₂ → d ∈ S) :
    FaceSetBoundary Delta (F₁ ∪ F₂) where
  faces_nonempty := by
    obtain ⟨f, hf⟩ := B₁.faces_nonempty
    exact ⟨f, Finset.mem_union_left F₂ hf⟩
  all_gCells := by
    intro face hface
    rcases Finset.mem_union.mp hface with h | h
    · exact B₁.all_gCells face h
    · exact B₂.all_gCells face h
  cycle := P ++ Q
  cycle_nonempty := List.append_ne_nil_of_left_ne_nil hP Q
  cycle_nodup := by
    have hn₁ : (P ++ S).Nodup := by
      rw [← h₁]
      exact B₁.cycle_nodup
    have hn₂ : (S.reverse.map Delta.toCombMap.alpha ++ Q).Nodup := by
      rw [← h₂]
      exact B₂.cycle_nodup
    refine List.nodup_append.mpr
      ⟨(List.nodup_append.mp hn₁).1, (List.nodup_append.mp hn₂).2.1, ?_⟩
    intro x hx y hy hxy
    have hx₁ : x ∈ B₁.cycle := by
      rw [h₁]
      exact List.mem_append_left S hx
    have hy₂ : y ∈ B₂.cycle := by
      rw [h₂]
      exact List.mem_append_right _ hy
    have hfx := ((B₁.cycle_mem_iff x).mp hx₁).1
    have hfy := ((B₂.cycle_mem_iff y).mp hy₂).1
    rw [hxy] at hfx
    exact Finset.disjoint_left.mp hdisj hfx hfy
  cycle_mem_iff := by
    intro d
    constructor
    · intro hd
      rcases List.mem_append.mp hd with hd | hd
      · exact FaceSetBoundary.glue_isBoundaryDart_left B₁ h₁ hadj hd
      · exact FaceSetBoundary.glue_isBoundaryDart_right B₂ h₂ hadj hd
    · intro hd
      exact FaceSetBoundary.glue_mem_of_isBoundaryDart B₁ B₂ h₁ h₂ hd
  cycle_chain := by
    have hc₁ : (P ++ S).IsChain (BoundaryStep Delta F₁) := by
      rw [← h₁]
      exact B₁.cycle_chain
    have hc₂ : (S.reverse.map Delta.toCombMap.alpha ++ Q).IsChain
        (BoundaryStep Delta F₂) := by
      rw [← h₂]
      exact B₂.cycle_chain
    obtain ⟨hcP, _, hj₁⟩ := List.isChain_append.mp hc₁
    obtain ⟨_, hcQ, hj₂⟩ := List.isChain_append.mp hc₂
    refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.IsChain.imp_of_mem_imp ?_ hcP
      intro a b ha hb hab
      exact ⟨FaceSetBoundary.glue_isBoundaryDart_left B₁ h₁ hadj ha,
        FaceSetBoundary.glue_isBoundaryDart_left B₁ h₁ hadj hb,
        reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_left hab.2.2⟩
    · refine List.IsChain.imp_of_mem_imp ?_ hcQ
      intro a b ha hb hab
      exact ⟨FaceSetBoundary.glue_isBoundaryDart_right B₂ h₂ hadj ha,
        FaceSetBoundary.glue_isBoundaryDart_right B₂ h₂ hadj hb,
        reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_right hab.2.2⟩
    · intro x hx y hy
      obtain ⟨hPne, rfl⟩ := List.mem_getLast?_eq_getLast hx
      have hyQ : y ∈ Q := by
        rw [glue_eq_head_of_mem_head? hQ hy]
        exact List.head_mem hQ
      obtain ⟨s, T, rfl⟩ := List.exists_cons_of_ne_nil hS
      have hstep₁ : BoundaryStep Delta F₁ (P.getLast hPne) s :=
        hj₁ (P.getLast hPne) hx s (by simp)
      have hstep₂ : BoundaryStep Delta F₂ (Delta.toCombMap.alpha s) y :=
        hj₂ (Delta.toCombMap.alpha s) (by simp [List.getLast?_map, List.getLast?_reverse]) y hy
      have hmove : InternalBoundaryMove Delta (F₁ ∪ F₂) s
          (Delta.toCombMap.facePerm (Delta.toCombMap.alpha s)) :=
        ⟨Finset.mem_union_left F₂ hstep₁.2.1.1, Finset.mem_union_right F₁ hstep₂.1.1, rfl⟩
      exact ⟨FaceSetBoundary.glue_isBoundaryDart_left B₁ h₁ hadj (List.getLast_mem hPne),
        FaceSetBoundary.glue_isBoundaryDart_right B₂ h₂ hadj hyQ,
        (reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_left hstep₁.2.2).trans
          (Relation.ReflTransGen.head hmove
            (reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_right
              hstep₂.2.2))⟩
  cycle_closes := by
    have hne₁ : P ++ S ≠ [] := List.append_ne_nil_of_left_ne_nil hP S
    have hne₂ : S.reverse.map Delta.toCombMap.alpha ++ Q ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hQ
    have hSne : S.reverse.map Delta.toCombMap.alpha ≠ [] := by
      simpa using hS
    have hclose₁ := B₁.cycle_closes
    have hclose₂ := B₂.cycle_closes
    rw [List.getLast_congr B₁.cycle_nonempty hne₁ h₁, List.getLast_append_of_ne_nil _ hS,
      glue_head_congr B₁.cycle_nonempty hne₁ h₁, List.head_append_of_ne_nil hP] at hclose₁
    rw [List.getLast_congr B₂.cycle_nonempty hne₂ h₂, List.getLast_append_of_ne_nil _ hQ,
      glue_head_congr B₂.cycle_nonempty hne₂ h₂, List.head_append_of_ne_nil hSne] at hclose₂
    have hhead : (S.reverse.map Delta.toCombMap.alpha).head hSne =
        Delta.toCombMap.alpha (S.getLast hS) := by
      simp
    rw [hhead] at hclose₂
    rw [List.getLast_append_of_ne_nil _ hQ, List.head_append_of_ne_nil hP]
    have hmove : InternalBoundaryMove Delta (F₁ ∪ F₂) (Delta.toCombMap.alpha (S.getLast hS))
        (Delta.toCombMap.facePerm (S.getLast hS)) := by
      refine ⟨Finset.mem_union_right F₁ hclose₂.2.1.1, ?_, ?_⟩
      · rw [Delta.toCombMap.alpha_involutive (S.getLast hS)]
        exact Finset.mem_union_left F₂ hclose₁.1.1
      · rw [Delta.toCombMap.alpha_involutive (S.getLast hS)]
    exact ⟨FaceSetBoundary.glue_isBoundaryDart_right B₂ h₂ hadj (List.getLast_mem hQ),
      FaceSetBoundary.glue_isBoundaryDart_left B₁ h₁ hadj (List.head_mem hP),
      (reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_right hclose₂.2.2).trans
        (Relation.ReflTransGen.head hmove
          (reflTransGen_internalBoundaryMove_of_subset Finset.subset_union_left
            hclose₁.2.2))⟩

/-- The glued cycle is `P ++ Q`. -/
@[simp] theorem FaceSetBoundary.glue_cycle {F₁ F₂ : Finset Delta.toCombMap.Face}
    (B₁ : FaceSetBoundary Delta F₁) (B₂ : FaceSetBoundary Delta F₂)
    (hdisj : Disjoint F₁ F₂) {P S Q : List Delta.toCombMap.Dart}
    (hP : P ≠ []) (hS : S ≠ []) (hQ : Q ≠ [])
    (h₁ : B₁.cycle = P ++ S) (h₂ : B₂.cycle = S.reverse.map Delta.toCombMap.alpha ++ Q)
    (hadj : ∀ d : Delta.toCombMap.Dart, Delta.toCombMap.faceOf d ∈ F₁ →
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈ F₂ → d ∈ S) :
    (B₁.glue B₂ hdisj hP hS hQ h₁ h₂ hadj).cycle = P ++ Q := rfl

end Glue

end Embedded
end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.glue_eq_head_of_mem_head?
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.glue_head_congr
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.internalBoundaryMove_of_subset
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.reflTransGen_internalBoundaryMove_of_subset
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.glue_isBoundaryDart_left
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.glue_isBoundaryDart_right
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.glue_mem_of_isBoundaryDart
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.glue
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.glue_cycle
