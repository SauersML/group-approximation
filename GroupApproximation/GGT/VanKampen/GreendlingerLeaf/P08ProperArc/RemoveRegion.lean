import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.ArcSplit
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Removing a region from the side of a noncrossing walk

Let `w = L ++ A⁻¹ ++ Mid ++ T` be a noncrossing closed walk with side `F`, and let `B` be the
boundary cycle `A⁻¹ ++ R ++ T ++ L` of a face set `Y` such that no internal dart of `Y` and no dart
of `R` is kept by `w`, with `T` nonempty.  Then (steps 3, 5, 6 of the proof in `ArcSplit`):

* every boundary face of `Y` is on the side of `w`;
* the boundary darts of `F \ Y` are exactly `R⁻¹ ++ Mid`;
* `R⁻¹ ++ Mid` is nodup and a closed walk.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc

universe u w v

open Embedded SimpleClosedWalkSides SameCellPocketWalk
open scoped Classical

/-- Membership in the first of four parts. -/
theorem mem4_1 {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α} (h : a ∈ l₁) :
    a ∈ l₁ ++ l₂ ++ l₃ ++ l₄ :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

/-- Membership in the second of four parts. -/
theorem mem4_2 {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α} (h : a ∈ l₂) :
    a ∈ l₁ ++ l₂ ++ l₃ ++ l₄ :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

/-- Membership in the third of four parts. -/
theorem mem4_3 {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α} (h : a ∈ l₃) :
    a ∈ l₁ ++ l₂ ++ l₃ ++ l₄ :=
  List.mem_append_left _ (List.mem_append_right _ h)

/-- Membership in the fourth of four parts. -/
theorem mem4_4 {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α} (h : a ∈ l₄) :
    a ∈ l₁ ++ l₂ ++ l₃ ++ l₄ :=
  List.mem_append_right _ h

/-- Membership in a four-part list. -/
theorem mem4_cases {α : Type*} {l₁ l₂ l₃ l₄ : List α} {a : α} (h : a ∈ l₁ ++ l₂ ++ l₃ ++ l₄) :
    a ∈ l₁ ∨ a ∈ l₂ ∨ a ∈ l₃ ∨ a ∈ l₄ := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **A boundary step of `Y` stays on one side of `w`**, when no internal dart of `Y` is kept. -/
theorem boundaryStep_iff (w : List X.toCombMap.Dart) {Yf : Finset X.toCombMap.Face}
    (hInt : ∀ t, X.toCombMap.faceOf t ∈ Yf → X.toCombMap.faceOf (X.toCombMap.alpha t) ∈ Yf →
      ¬ walkKeep X.toCombMap w t) :
    ∀ a b, BoundaryStep X Yf a b →
      (X.toCombMap.faceOf a ∈ sideFaces X.toCombMap w ↔
        X.toCombMap.faceOf b ∈ sideFaces X.toCombMap w) := by
  rintro a b ⟨-, -, hmove⟩
  rw [← X.toCombMap.faceOf_facePerm a]
  induction hmove with
  | refl => exact Iff.rfl
  | @tail b' _ _ hstep ih =>
    obtain ⟨h1, h2, rfl⟩ := hstep
    rw [X.toCombMap.faceOf_facePerm (X.toCombMap.alpha b')]
    exact ih.trans (mem_sideFaces_iff_of_not_walkKeep w (hInt _ h1 h2))

/-- **Every boundary face of `Y` is on the side of `w`**, given one boundary dart of `Y` on `w`. -/
theorem cycle_faces_mem {w : List X.toCombMap.Dart} {Yf : Finset X.toCombMap.Face}
    (hw : IsNoncrossingClosedWalk X.toCombMap w) (B : FaceSetBoundary X Yf)
    (hInt : ∀ t, X.toCombMap.faceOf t ∈ Yf → X.toCombMap.faceOf (X.toCombMap.alpha t) ∈ Yf →
      ¬ walkKeep X.toCombMap w t)
    {d₀ : X.toCombMap.Dart} (hd₀w : d₀ ∈ w) (hd₀c : d₀ ∈ B.cycle) :
    ∀ d ∈ B.cycle, X.toCombMap.faceOf d ∈ sideFaces X.toCombMap w := by
  intro d hd
  have hF : X.toCombMap.faceOf d₀ ∈ sideFaces X.toCombMap w :=
    And.left ((hw.isBoundaryDart_sideFaces_iff X.planar d₀).mpr hd₀w)
  exact (iff_of_isChain (Q := fun e => X.toCombMap.faceOf e ∈ sideFaces X.toCombMap w)
    (boundaryStep_iff w hInt) B.cycle_chain d hd d₀ hd₀c).mpr hF

section Remove

variable {w : List X.toCombMap.Dart} {Yf : Finset X.toCombMap.Face}
  {L A Mid T R : List X.toCombMap.Dart}

/-- (→) of step 5: a boundary dart of `F \ Y` lies on `R⁻¹ ++ Mid`. -/
theorem mem_of_isBoundaryDart_sdiff (hw : IsNoncrossingClosedWalk X.toCombMap w)
    (B : FaceSetBoundary X Yf) (hwalk : w = L ++ invDarts X A ++ Mid ++ T)
    (hcyc : B.cycle = invDarts X A ++ R ++ T ++ L) (d : X.toCombMap.Dart)
    (hd : Surgery.MapCollapse.IsBoundaryDart X.toCombMap (sideFaces X.toCombMap w \ Yf) d) :
    d ∈ invDarts X R ++ Mid := by
  have hmw : ∀ e, e ∈ L ++ invDarts X A ++ Mid ++ T → e ∈ w := fun e he => by
    rw [hwalk]; exact he
  have hcw : ∀ e, e ∈ w → e ∈ L ++ invDarts X A ++ Mid ++ T := fun e he => by
    rw [← hwalk]; exact he
  have hcyc4 : ∀ e, e ∈ B.cycle → e ∈ invDarts X A ++ R ++ T ++ L := fun e he => by
    rw [← hcyc]; exact he
  obtain ⟨hdF', hαF'⟩ := hd
  obtain ⟨hdF, hdY⟩ := Finset.mem_sdiff.mp hdF'
  by_cases hαF : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ sideFaces X.toCombMap w
  · have hαY : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ Yf := by
      by_contra h
      exact hαF' (Finset.mem_sdiff.mpr ⟨hαF, h⟩)
    have hαc : X.toCombMap.alpha d ∈ B.cycle :=
      (B.cycle_mem_iff _).mpr ⟨hαY, by rw [X.toCombMap.alpha_involutive d]; exact hdY⟩
    have hnotw : X.toCombMap.alpha d ∉ w := fun h => by
      have hb := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr h)
      rw [X.toCombMap.alpha_involutive d] at hb
      exact hb hdF
    rcases mem4_cases (hcyc4 _ hαc) with h | h | h | h
    · exact (hnotw (hmw _ (mem4_2 h))).elim
    · exact List.mem_append_left _ (mem_invDarts_of_alpha_mem h)
    · exact (hnotw (hmw _ (mem4_4 h))).elim
    · exact (hnotw (hmw _ (mem4_1 h))).elim
  · have hdw : d ∈ w := (hw.isBoundaryDart_sideFaces_iff X.planar d).mp ⟨hdF, hαF⟩
    have hcycm : ∀ e, e ∈ invDarts X A ++ R ++ T ++ L → e ∈ B.cycle := fun e he => by
      rw [hcyc]; exact he
    rcases mem4_cases (hcw _ hdw) with h | h | h | h
    · exact (hdY (And.left ((B.cycle_mem_iff d).mp (hcycm _ (mem4_4 h))))).elim
    · exact (hdY (And.left ((B.cycle_mem_iff d).mp (hcycm _ (mem4_1 h))))).elim
    · exact List.mem_append_right _ h
    · exact (hdY (And.left ((B.cycle_mem_iff d).mp (hcycm _ (mem4_3 h))))).elim

/-- (←) of step 5: a dart of `R⁻¹ ++ Mid` is a boundary dart of `F \ Y`. -/
theorem isBoundaryDart_sdiff_of_mem (hw : IsNoncrossingClosedWalk X.toCombMap w)
    (B : FaceSetBoundary X Yf) (hwalk : w = L ++ invDarts X A ++ Mid ++ T)
    (hcyc : B.cycle = invDarts X A ++ R ++ T ++ L)
    (hInt : ∀ t, X.toCombMap.faceOf t ∈ Yf → X.toCombMap.faceOf (X.toCombMap.alpha t) ∈ Yf →
      ¬ walkKeep X.toCombMap w t)
    (hR : ∀ e ∈ R, ¬ walkKeep X.toCombMap w e)
    (hcycF : ∀ e ∈ B.cycle, X.toCombMap.faceOf e ∈ sideFaces X.toCombMap w)
    (d : X.toCombMap.Dart) (hd : d ∈ invDarts X R ++ Mid) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap (sideFaces X.toCombMap w \ Yf) d := by
  have hcycm : ∀ e, e ∈ invDarts X A ++ R ++ T ++ L → e ∈ B.cycle := fun e he => by
    rw [hcyc]; exact he
  rcases List.mem_append.mp hd with h | h
  · have hαR := alpha_mem_of_mem_invDarts h
    have hαc : X.toCombMap.alpha d ∈ B.cycle := hcycm _ (mem4_2 hαR)
    have hαY : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ Yf :=
      And.left ((B.cycle_mem_iff _).mp hαc)
    have hdY : X.toCombMap.faceOf d ∉ Yf := by
      have hb := And.right ((B.cycle_mem_iff _).mp hαc)
      rw [X.toCombMap.alpha_involutive d] at hb
      exact hb
    have hdF : X.toCombMap.faceOf d ∈ sideFaces X.toCombMap w := by
      have hk := (mem_sideFaces_iff_of_not_walkKeep w (hR _ hαR)).mp (hcycF _ hαc)
      rw [X.toCombMap.alpha_involutive d] at hk
      exact hk
    exact ⟨Finset.mem_sdiff.mpr ⟨hdF, hdY⟩, fun hα => (Finset.mem_sdiff.mp hα).2 hαY⟩
  · have hdw : d ∈ w := by rw [hwalk]; exact mem4_3 h
    have hb := (hw.isBoundaryDart_sideFaces_iff X.planar d).mpr hdw
    refine ⟨Finset.mem_sdiff.mpr ⟨And.left hb, fun hdY => ?_⟩,
      fun hα => And.right hb (Finset.mem_sdiff.mp hα).1⟩
    by_cases hαY : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ Yf
    · exact hInt d hdY hαY (Or.inl hdw)
    · have hdc : d ∈ invDarts X A ++ R ++ T ++ L := by
        rw [← hcyc]; exact (B.cycle_mem_iff d).mpr ⟨hdY, hαY⟩
      have hwn : (L ++ invDarts X A ++ Mid ++ T).Nodup := by rw [← hwalk]; exact hw.nodup
      obtain ⟨hnL, hnA, hnT⟩ := not_mem_of_nodup_mid hwn h
      rcases mem4_cases hdc with h' | h' | h' | h'
      · exact hnA h'
      · exact hR d h' (Or.inl hdw)
      · exact hnT h'
      · exact hnL h'

/-- Step 6: the new cycle `R⁻¹ ++ Mid` is nodup. -/
theorem newCycle_nodup (hw : IsNoncrossingClosedWalk X.toCombMap w)
    (B : FaceSetBoundary X Yf) (hwalk : w = L ++ invDarts X A ++ Mid ++ T)
    (hcyc : B.cycle = invDarts X A ++ R ++ T ++ L)
    (hR : ∀ e ∈ R, ¬ walkKeep X.toCombMap w e) :
    (invDarts X R ++ Mid).Nodup := by
  have hBn : (invDarts X A ++ R ++ T ++ L).Nodup := by rw [← hcyc]; exact B.cycle_nodup
  have hwn : (L ++ invDarts X A ++ Mid ++ T).Nodup := by rw [← hwalk]; exact hw.nodup
  have hRn : R.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hBn).1).1).2.1
  have hMidn : Mid.Nodup := (List.nodup_append.mp (List.nodup_append.mp hwn).1).2.1
  refine List.nodup_append.mpr
    ⟨(List.nodup_reverse.mpr hRn).map X.toCombMap.alpha_involutive.injective, hMidn, ?_⟩
  intro a ha b hb hab
  refine hR _ (alpha_mem_of_mem_invDarts ha) (Or.inr ?_)
  rw [X.toCombMap.alpha_involutive a, hab, hwalk]
  exact mem4_3 hb

/-- Step 6: the new cycle `R⁻¹ ++ Mid` is a closed walk. -/
theorem newCycle_closed (hw : IsNoncrossingClosedWalk X.toCombMap w)
    (B : FaceSetBoundary X Yf) (hwalk : w = L ++ invDarts X A ++ Mid ++ T)
    (hcyc : B.cycle = invDarts X A ++ R ++ T ++ L)
    (hA : A ≠ []) (hT : T ≠ []) (hMid : Mid ≠ []) :
    IsClosedDartWalk X.toCombMap (invDarts X R ++ Mid) := by
  obtain ⟨_, hW⟩ : ∃ p, IsWalkFromTo X.toCombMap w p p := ⟨_, isWalkFromTo_of_noncrossing hw⟩
  obtain ⟨_, hC⟩ : ∃ p, IsWalkFromTo X.toCombMap B.cycle p p :=
    ⟨_, isWalkFromTo_of_isChain_closes B.cycle_nonempty B.isChain_closes.1 B.isChain_closes.2⟩
  rw [hwalk] at hW
  rw [hcyc] at hC
  obtain ⟨v₃, hW123, hWT⟩ := hW.exists_split
  obtain ⟨v₂, hW12, hWM⟩ := hW123.exists_split
  obtain ⟨_, -, hWA⟩ := hW12.exists_split
  obtain ⟨_, hC123, -⟩ := hC.exists_split
  obtain ⟨p₂, hC12, hCT⟩ := hC123.exists_split
  obtain ⟨p₁, hCA, hCR⟩ := hC12.exists_split
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil A hA
  have hinvA : invDarts X A ≠ [] :=
    List.ne_nil_of_mem (List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr ha))
  have h12 : v₂ = p₁ := (hWA.eq_of_ne_nil hCA hinvA).2
  have h23 : v₃ = p₂ := (hWT.eq_of_ne_nil hCT hT).1
  have hRinv : IsWalkFromTo X.toCombMap (invDarts X R) p₂ p₁ := hCR.reverse_map
  rw [h12, h23] at hWM
  exact (hRinv.append hWM).isClosedDartWalk (List.append_ne_nil_of_right_ne_nil _ hMid)

end Remove

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem4_1
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem4_2
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem4_3
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem4_4
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem4_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.boundaryStep_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.cycle_faces_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.mem_of_isBoundaryDart_sdiff
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.isBoundaryDart_sdiff_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.newCycle_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.newCycle_closed
