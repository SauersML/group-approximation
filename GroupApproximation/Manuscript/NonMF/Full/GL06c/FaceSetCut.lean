import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Cutting a region off a face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), and `thm:hull` (non_mf_groups_exist.tex,
"Hull's small cancellation theorem", ~2121): the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.
When a region `Γ_{i,1}` lies inside `Γ_1` and its boundary `u ++ L` shares the stretch `u` with
`∂Γ_1 = A ++ u ++ B`, removing the faces of the region leaves a face set with boundary
`A ++ L⁻¹ ++ B`.

* `mem_invDarts_iff`: a dart lies on `L⁻¹` iff its reverse lies on `L`.
* `mem_cut_iff`: the boundary darts of `P \ R` are the darts of `A ++ L⁻¹ ++ B`.
* `nodup_cut`: that list has no repeated darts.
* `isChain_closes_cut`: if `A ++ u ++ B` and `u ++ L` are closed walks, so is `A ++ L⁻¹ ++ B`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex) through Osin's Lemma 9.7(b); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06c

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded

universe u w v

section Walks

variable {α : Type*} {R : α → α → Prop}

/-- A relation between the last and first entries of a nonempty list, in `Option` form. -/
theorem cut_closes_of_last_head {l : List α} (hne : l ≠ [])
    (h : R (l.getLast hne) (l.head hne)) : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b := by
  intro a ha b hb
  obtain rfl := Option.some.inj
    ((List.getLast?_eq_some_getLast hne).symm.trans (Option.mem_def.mp ha))
  obtain rfl := Option.some.inj
    ((List.head?_eq_some_head hne).symm.trans (Option.mem_def.mp hb))
  exact h

/-- The `Option` form of the closing relation gives the relation between last and first. -/
theorem cut_last_head_of_closes {l : List α} (hne : l ≠ [])
    (h : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b) : R (l.getLast hne) (l.head hne) :=
  h _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast hne)) _
    (Option.mem_def.mpr (List.head?_eq_some_head hne))

end Walks

section Cut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- A dart lies on a dart list read backwards iff its reverse lies on the list. -/
theorem mem_invDarts_iff (X : DiscDiagram.{u, w, v} W) {l : List X.toCombMap.Dart}
    {d : X.toCombMap.Dart} : d ∈ invDarts X l ↔ X.toCombMap.alpha d ∈ l := by
  simp only [invDarts, List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [X.toCombMap.alpha_involutive e]
    exact he
  · intro h
    exact ⟨X.toCombMap.alpha d, h, X.toCombMap.alpha_involutive d⟩

/-- A nonempty dart list read backwards is nonempty. -/
theorem invDarts_ne_nil {l : List X.toCombMap.Dart} (h : l ≠ []) : invDarts X l ≠ [] := by
  intro h'
  apply h
  apply List.eq_nil_of_length_eq_zero
  have hlen := congrArg List.length h'
  simp only [invDarts, List.length_map, List.length_reverse, List.length_nil] at hlen
  exact hlen

/-- **The boundary of a face set with a region cut off** (`thm:hull`, Osin Lemma 9.7(b)).  Let the
boundary darts of `P` be the darts of `A ++ Mid ++ B`, without repetition, and let the boundary darts
of `R ⊆ P` be the darts of `Mid ++ L`, where no dart of `L` lies on `A ++ Mid ++ B`.  Then the
boundary darts of `P \ R` are the darts of `A ++ L⁻¹ ++ B`. -/
theorem mem_cut_iff [DecidableEq X.toCombMap.Face] {P R : Finset X.toCombMap.Face}
    {A Mid L B : List X.toCombMap.Dart}
    (hP : ∀ d, d ∈ A ++ Mid ++ B ↔
      (X.toCombMap.faceOf d ∈ P ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P))
    (hR : ∀ d, d ∈ Mid ++ L ↔
      (X.toCombMap.faceOf d ∈ R ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R))
    (hRP : R ⊆ P) (hnodup : (A ++ Mid ++ B).Nodup) (hL : ∀ e ∈ L, e ∉ A ++ Mid ++ B) :
    ∀ d, d ∈ A ++ invDarts X L ++ B ↔
      (X.toCombMap.faceOf d ∈ P \ R ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P \ R) := by
  obtain ⟨hAM, -, hAMB⟩ := List.nodup_append.mp hnodup
  obtain ⟨-, -, hAMid⟩ := List.nodup_append.mp hAM
  intro d
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · intro hd
    rcases List.mem_append.mp hd with hd' | hB
    · rcases List.mem_append.mp hd' with hA | hJ
      · have hw : d ∈ A ++ Mid ++ B := List.mem_append_left B (List.mem_append_left Mid hA)
        obtain ⟨hdP, hdaP⟩ := (hP d).mp hw
        refine ⟨⟨hdP, fun hdR => ?_⟩, fun h => hdaP h.1⟩
        have hdaR : X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R := fun h => hdaP (hRP h)
        rcases List.mem_append.mp ((hR d).mpr ⟨hdR, hdaR⟩) with hM | hL'
        · exact hAMid d hA d hM rfl
        · exact hL d hL' hw
      · have ha : X.toCombMap.alpha d ∈ L := (mem_invDarts_iff X).mp hJ
        obtain ⟨haR, haaR⟩ := (hR _).mp (List.mem_append_right Mid ha)
        rw [X.toCombMap.alpha_involutive d] at haaR
        refine ⟨⟨?_, haaR⟩, fun h => h.2 haR⟩
        by_contra hdP
        refine hL _ ha ((hP _).mpr ⟨hRP haR, ?_⟩)
        rw [X.toCombMap.alpha_involutive d]
        exact hdP
    · have hw : d ∈ A ++ Mid ++ B := List.mem_append_right (A ++ Mid) hB
      obtain ⟨hdP, hdaP⟩ := (hP d).mp hw
      refine ⟨⟨hdP, fun hdR => ?_⟩, fun h => hdaP h.1⟩
      have hdaR : X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R := fun h => hdaP (hRP h)
      rcases List.mem_append.mp ((hR d).mpr ⟨hdR, hdaR⟩) with hM | hL'
      · exact hAMB d (List.mem_append_right A hM) d hB rfl
      · exact hL d hL' hw
  · rintro ⟨⟨hdP, hdR⟩, hda⟩
    by_cases haP : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ P
    · have haR : X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ R := by
        by_contra h
        exact hda ⟨haP, h⟩
      have haM : X.toCombMap.alpha d ∈ Mid ++ L := by
        refine (hR _).mpr ⟨haR, ?_⟩
        rw [X.toCombMap.alpha_involutive d]
        exact hdR
      rcases List.mem_append.mp haM with hM | hL'
      · have hw : X.toCombMap.alpha d ∈ A ++ Mid ++ B :=
          List.mem_append_left B (List.mem_append_right A hM)
        have h := ((hP _).mp hw).2
        rw [X.toCombMap.alpha_involutive d] at h
        exact absurd hdP h
      · exact List.mem_append_left B (List.mem_append_right A ((mem_invDarts_iff X).mpr hL'))
    · have hw : d ∈ A ++ Mid ++ B := (hP d).mpr ⟨hdP, haP⟩
      rcases List.mem_append.mp hw with hAM' | hB
      · rcases List.mem_append.mp hAM' with hA | hM
        · exact List.mem_append_left B (List.mem_append_left _ hA)
        · exact absurd ((hR d).mp (List.mem_append_left L hM)).1 hdR
      · exact List.mem_append_right _ hB

/-- **The cut boundary has no repeated darts.** -/
theorem nodup_cut {P R : Finset X.toCombMap.Face} {A Mid L B : List X.toCombMap.Dart}
    (hP : ∀ d, d ∈ A ++ Mid ++ B ↔
      (X.toCombMap.faceOf d ∈ P ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ P))
    (hR : ∀ d, d ∈ Mid ++ L ↔
      (X.toCombMap.faceOf d ∈ R ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ R))
    (hRP : R ⊆ P) (hnodup : (A ++ Mid ++ B).Nodup) (hRnodup : (Mid ++ L).Nodup) :
    (A ++ invDarts X L ++ B).Nodup := by
  obtain ⟨hAM, hBn, hAMB⟩ := List.nodup_append.mp hnodup
  obtain ⟨hAn, -, -⟩ := List.nodup_append.mp hAM
  have hLn : L.Nodup := (List.nodup_append.mp hRnodup).2.1
  have hJn : (invDarts X L).Nodup :=
    List.Nodup.map X.toCombMap.alpha.injective (List.nodup_reverse.mpr hLn)
  have hoff : ∀ e ∈ invDarts X L, e ∉ A ++ Mid ++ B := by
    intro e he hw
    have ha : X.toCombMap.alpha e ∈ Mid ++ L :=
      List.mem_append_right Mid ((mem_invDarts_iff X).mp he)
    exact ((hP e).mp hw).2 (hRP ((hR _).mp ha).1)
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hAn, hJn, ?_⟩, hBn, ?_⟩
  · intro a ha b hb hab
    rw [← hab] at hb
    exact hoff a hb (List.mem_append_left B (List.mem_append_left Mid ha))
  · intro a ha b hb hab
    rw [← hab] at hb
    rcases List.mem_append.mp ha with ha' | ha'
    · exact hAMB a (List.mem_append_left Mid ha') a hb rfl
    · exact hoff a ha' (List.mem_append_right (A ++ Mid) hb)

/-- **The cut boundary is a closed walk** (`thm:hull`, Osin Lemma 9.7(b)).  If `A ++ Mid ++ B` and
`Mid ++ L` are closed walks, with `A`, `Mid`, `B` nonempty, then `A ++ L⁻¹ ++ B` is a closed walk:
`L⁻¹` runs from the start of `Mid` back to its end. -/
theorem isChain_closes_cut {A Mid L B : List X.toCombMap.Dart}
    (hA : A ≠ []) (hMid : Mid ≠ []) (hB : B ≠ [])
    (hw : (A ++ Mid ++ B).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hwc : ∀ a ∈ (A ++ Mid ++ B).getLast?, ∀ b ∈ (A ++ Mid ++ B).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b)
    (hx : (Mid ++ L).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hxc : ∀ a ∈ (Mid ++ L).getLast?, ∀ b ∈ (Mid ++ L).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) :
    ((A ++ invDarts X L ++ B).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      ∀ a ∈ (A ++ invDarts X L ++ B).getLast?, ∀ b ∈ (A ++ invDarts X L ++ B).head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
  obtain ⟨hwAM, hwB, hjB⟩ := List.isChain_append.mp hw
  obtain ⟨hwA, -, hjM⟩ := List.isChain_append.mp hwAM
  obtain ⟨-, hxL, hjL⟩ := List.isChain_append.mp hx
  have hm0 : Mid.head hMid ∈ Mid.head? := Option.mem_def.mpr (List.head?_eq_some_head hMid)
  have hm1 : Mid.getLast hMid ∈ Mid.getLast? :=
    Option.mem_def.mpr (List.getLast?_eq_some_getLast hMid)
  have hm1' : Mid.getLast hMid ∈ (A ++ Mid).getLast? :=
    List.mem_getLast?_append_of_mem_getLast? hm1
  have hJ : (invDarts X L).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
    isChain_invDarts (Delta := X) hxL
  refine ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨hwA, hJ, ?_⟩, hwB, ?_⟩, ?_⟩
  · intro a ha b hb
    rw [head?_invDarts, Option.mem_def, Option.map_eq_some_iff] at hb
    obtain ⟨l, hl, rfl⟩ := hb
    have hl' : l ∈ (Mid ++ L).getLast? :=
      List.mem_getLast?_append_of_mem_getLast? (Option.mem_def.mpr hl)
    have hm0' : Mid.head hMid ∈ (Mid ++ L).head? := List.mem_head?_append_of_mem_head? hm0
    exact Eq.trans (hjM a ha _ hm0) (Eq.symm (hxc l hl' _ hm0'))
  · intro a ha b hb
    have hE2 : X.toCombMap.vertexOf (X.toCombMap.alpha (Mid.getLast hMid)) =
        X.toCombMap.vertexOf b := hjB _ hm1' b hb
    by_cases hL : L = []
    · subst hL
      rw [show invDarts X ([] : List X.toCombMap.Dart) = [] from rfl, List.append_nil] at ha
      rw [List.append_nil] at hxc
      exact Eq.trans (hjM a ha _ hm0) (Eq.trans (Eq.symm (hxc _ hm1 _ hm0)) hE2)
    · rw [List.getLast?_append_of_ne_nil _ (invDarts_ne_nil hL), getLast?_invDarts,
        Option.mem_def, Option.map_eq_some_iff] at ha
      obtain ⟨l0, hl0, rfl⟩ := ha
      show X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha l0)) =
        X.toCombMap.vertexOf b
      rw [X.toCombMap.alpha_involutive l0]
      exact Eq.trans (Eq.symm (hjL _ hm1 _ (Option.mem_def.mpr hl0))) hE2
  · intro a ha b hb
    rw [List.getLast?_append_of_ne_nil _ hB] at ha
    rw [List.head?_append_of_ne_nil _ (List.append_ne_nil_of_left_ne_nil hA _),
      List.head?_append_of_ne_nil _ hA] at hb
    exact hwc a (List.mem_getLast?_append_of_mem_getLast? ha) b
      (List.mem_head?_append_of_mem_head? (List.mem_head?_append_of_mem_head? hb))

end Cut

end GroupApproximation.Full.GL06c

#audit_axioms GroupApproximation.Full.GL06c.cut_closes_of_last_head
#audit_axioms GroupApproximation.Full.GL06c.cut_last_head_of_closes
#audit_axioms GroupApproximation.Full.GL06c.mem_invDarts_iff
#audit_axioms GroupApproximation.Full.GL06c.invDarts_ne_nil
#audit_axioms GroupApproximation.Full.GL06c.mem_cut_iff
#audit_axioms GroupApproximation.Full.GL06c.nodup_cut
#audit_axioms GroupApproximation.Full.GL06c.isChain_closes_cut
