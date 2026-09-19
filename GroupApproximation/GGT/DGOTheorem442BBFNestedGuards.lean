import GroupApproximation.GGT.DGOTheorem442BBFGuards

/-!
# Nested BBF guards

This file proves the finite-order selection lemmas and the nested-guards lemma
following Bestvina--Bromberg--Fujiwara Lemma 3.18.  The graph threshold is
taken at least `64ξ`, which simultaneously covers the half-threshold order and
the explicit `8ξ` move bound.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- A blocker of `(W,Z)` is also a blocker of `(X,Z)` when `W` is a large
projection of `(X,Z)`.  This is the monotonicity inclusion used throughout
the guards argument. -/
theorem bbf_blocker_transfer_of_large
    (P : ProjectionSystem V) {T S : ℝ}
    (hT : 4 * P.ξ ≤ T) (hS : P.ξ ≤ S)
    {X Z W U : V}
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers T X Z)
    (hU : U ∈ (ProjectionPerturbation.bbf P).blockers S W Z) :
    U ∈ (ProjectionPerturbation.bbf P).blockers S X Z := by
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hT, P.ξ_pos]) hW
  change W ≠ X ∧ W ≠ Z ∧ T < P.bbfProjDist W X Z at hW
  change U ≠ W ∧ U ≠ Z ∧ S < P.bbfProjDist U W Z at hU
  have hUX : U ≠ X := by
    intro hUX
    subst U
    have hend := P.bbfProjDist_endpoints_lt hW.1 hW.2.1 hXZ (by
      linarith [hW.2.2, hT, P.ξ_pos])
    linarith [hU.2.2, hend.1, hS]
  have hmono := P.bbfProjDist_right_mono hUX hU.1 hU.2.1
    hW.1 hW.2.1 hXZ (by linarith [hW.2.2, hT, P.ξ_pos])
  rw [P.bbfProjDist_comm U Z W] at hmono
  exact ⟨hUX, hU.2.1, hU.2.2.trans_le hmono⟩

/-- In the finite `(K/2)`-large set, any nonempty initial segment cut out by
`U < W` has a greatest element. -/
theorem exists_maximal_half_blocker_before
    (P : ProjectionSystem V) {K : ℝ} (hK : 24 * P.ξ ≤ K)
    {X Z W : V}
    (hW : W ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z)
    (hseed : ∃ U,
      U ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z ∧
      5 * P.ξ < P.bbfProjDist U X W) :
    ∃ W',
      W' ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z ∧
      5 * P.ξ < P.bbfProjDist W' X W ∧
      ∀ U,
        U ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z →
        5 * P.ξ < P.bbfProjDist U X W →
        U = W' ∨ 5 * P.ξ < P.bbfProjDist U X W' := by
  classical
  have hhalf : 12 * P.ξ ≤ K / 2 := by
    linarith [hK]
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [P.ξ_pos]) hW
  obtain ⟨L, _hnodup, hmem, hpair⟩ :=
    P.exists_bbf_large_projection_list hhalf hXZ
  let C : List V := L.filter fun U =>
    5 * P.ξ < P.bbfProjDist U X W
  obtain ⟨U₀, hU₀, hU₀W⟩ := hseed
  have hU₀C : U₀ ∈ C := by
    dsimp only [C]
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨(hmem U₀).mpr hU₀, hU₀W⟩
  have hCne : C ≠ [] := List.ne_nil_of_mem hU₀C
  let W' : V := C.getLast hCne
  have hW'C : W' ∈ C := by
    exact List.getLast_mem hCne
  have hW'parts : W' ∈ L ∧
      5 * P.ξ < P.bbfProjDist W' X W := by
    dsimp only [C] at hW'C
    simpa only [decide_eq_true_eq] using List.mem_filter.mp hW'C
  have hW'block := (hmem W').mp hW'parts.1
  refine ⟨W', hW'block, hW'parts.2, ?_⟩
  intro U hU hUW
  have hUC : U ∈ C := by
    dsimp only [C]
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨(hmem U).mpr hU, hUW⟩
  have hpairC : C.Pairwise (fun A B =>
      5 * P.ξ < P.bbfProjDist A X B) := by
    dsimp only [C]
    exact hpair.filter _
  have hpairRefl : C.Pairwise (fun A B =>
      A = B ∨ 5 * P.ξ < P.bbfProjDist A X B) :=
    hpairC.imp fun h => Or.inr h
  have hrel := hpairRefl.rel_getLast_of_rel_getLast_getLast hUC (Or.inl rfl)
  simpa only [W'] using hrel

/-- Every non-edge `(X,Z)` admits a guard for `Z` which is a `(K/2)`-large
projection from `X`.  This is the initial-guard choice in the proof of BBF's
key barrier proposition. -/
theorem exists_isBBFGuard_mem_half_blockers_of_not_adj
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {X Z : V} (hXZ : X ≠ Z)
    (hnot : ¬ ((ProjectionPerturbation.bbf P).graph K).Adj X Z) :
    ∃ W,
      IsBBFGuard P K W Z ∧
      W ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z := by
  classical
  have hhalf : 12 * P.ξ ≤ K / 2 := by
    calc
      12 * P.ξ ≤ 32 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K / 2 := by linarith [hK]
  have hKhalf : K / 2 < K := by
    linarith [hK, P.ξ_pos]
  have hblockers : (ProjectionPerturbation.bbf P).blockers K X Z ≠ ∅ := by
    intro hempty
    apply hnot
    exact (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty
      (ProjectionPerturbation.bbf P) K X Z).mpr ⟨hXZ, hempty⟩
  obtain ⟨U₀, hU₀⟩ :
      ((ProjectionPerturbation.bbf P).blockers K X Z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hblockers
  have hU₀half : U₀ ∈
      (ProjectionPerturbation.bbf P).blockers (K / 2) X Z := by
    change U₀ ≠ X ∧ U₀ ≠ Z ∧ K / 2 < P.bbfProjDist U₀ X Z
    change U₀ ≠ X ∧ U₀ ≠ Z ∧ K < P.bbfProjDist U₀ X Z at hU₀
    exact ⟨hU₀.1, hU₀.2.1, hKhalf.trans hU₀.2.2⟩
  obtain ⟨L, _hnodup, hmem, hpair⟩ :=
    P.exists_bbf_large_projection_list hhalf hXZ
  have hLne : L ≠ [] := by
    exact List.ne_nil_of_mem ((hmem U₀).mpr hU₀half)
  let W : V := L.getLast hLne
  have hWmem : W ∈ L := List.getLast_mem hLne
  have hWhalf : W ∈
      (ProjectionPerturbation.bbf P).blockers (K / 2) X Z :=
    (hmem W).mp hWmem
  have hempty :
      (ProjectionPerturbation.bbf P).blockers (K / 2) W Z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro U hU
    have hUtransfer := P.bbf_blocker_transfer_of_large
      (T := K / 2) (S := K / 2) (by linarith [hhalf, P.ξ_pos])
      (by linarith [hhalf, P.ξ_pos]) hWhalf hU
    have hUmem : U ∈ L := (hmem U).mpr hUtransfer
    have hpairRefl : L.Pairwise (fun A B =>
        A = B ∨ 5 * P.ξ < P.bbfProjDist A X B) :=
      hpair.imp fun h => Or.inr h
    have hrel :=
      hpairRefl.rel_getLast_of_rel_getLast_getLast hUmem (Or.inl rfl)
    have hrel' : U = W ∨ 5 * P.ξ < P.bbfProjDist U X W := by
      simpa only [W] using hrel
    rcases hrel' with hUW | hbefore
    · change U ≠ W ∧ U ≠ Z ∧ K / 2 < P.bbfProjDist U W Z at hU
      exact hU.1 hUW
    · have hUW : U ≠ W := P.ne_of_bbf_before hbefore
      have hsmall :=
        (P.bbf_before_consequences hhalf hUtransfer hWhalf hUW hbefore).2.2
      change U ≠ W ∧ U ≠ Z ∧ K / 2 < P.bbfProjDist U W Z at hU
      linarith [hU.2.2, hsmall, hhalf, P.ξ_pos]
  have hW12 : W ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z := by
    change W ≠ X ∧ W ≠ Z ∧ 12 * P.ξ < P.bbfProjDist W X Z
    change W ≠ X ∧ W ≠ Z ∧ K / 2 < P.bbfProjDist W X Z at hWhalf
    exact ⟨hWhalf.1, hWhalf.2.1, lt_of_le_of_lt hhalf hWhalf.2.2⟩
  have hguard := P.isBBFGuard_of_half_blockers_eq_empty
    (by linarith [hK]) hW12 hempty
  exact ⟨W, hguard, hWhalf⟩

/-- **BBF nested-guards lemma.**  When a guard ceases to be `(K/2)`-large
after moving across one graph edge, a new guard can be chosen below it.  The
old guard is then `12ξ`-large from the new guard's viewpoint. -/
theorem exists_nested_isBBFGuard
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {X₀ X₁ Z W : V}
    (h01 : ((ProjectionPerturbation.bbf P).graph K).Adj X₀ X₁)
    (hguard : IsBBFGuard P K W Z)
    (hW₀ : W ∈
      (ProjectionPerturbation.bbf P).blockers (K / 2) X₀ Z)
    (hW₁not : W ∉
      (ProjectionPerturbation.bbf P).blockers (K / 2) X₁ Z)
    (h0Wnot : ¬ ((ProjectionPerturbation.bbf P).graph K).Adj X₀ W)
    (hX₁W : X₁ ≠ W) (hX₁Z : X₁ ≠ Z)
    (hX₁Znot : ¬ ((ProjectionPerturbation.bbf P).graph K).Adj X₁ Z) :
    ∃ W',
      IsBBFGuard P K W' Z ∧
      W' ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X₁ Z ∧
      W ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) W' Z := by
  have hhalf : 12 * P.ξ ≤ K / 2 := by
    calc
      12 * P.ξ ≤ 32 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K / 2 := by linarith [hK]
  have hK12 : 12 * P.ξ ≤ K := by
    calc
      12 * P.ξ ≤ 64 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K := hK
  have hK24 : 24 * P.ξ ≤ K := by
    calc
      24 * P.ξ ≤ 64 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K := hK
  have hX₀Z : X₀ ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hhalf, P.ξ_pos]) hW₀
  change W ≠ X₀ ∧ W ≠ Z ∧ K / 2 < P.bbfProjDist W X₀ Z at hW₀
  have hmove := P.abs_bbfProjDist_sub_le_eight_mul_of_adj_of_not_adj
    hK12 h01 hW₀.1.symm h0Wnot hW₀.2.1
      hX₀Z hX₁Z
  have hW₁strong : K / 2 - 8 * P.ξ < P.bbfProjDist W X₁ Z := by
    have hupper := (abs_le.mp hmove).2
    linarith [hW₀.2.2]
  have hW₁12 : W ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X₁ Z := by
    change W ≠ X₁ ∧ W ≠ Z ∧ 12 * P.ξ < P.bbfProjDist W X₁ Z
    refine ⟨hX₁W.symm, hW₀.2.1, ?_⟩
    linarith [hW₁strong, hK, P.ξ_pos]
  have hblockers : (ProjectionPerturbation.bbf P).blockers K X₁ Z ≠ ∅ := by
    intro hempty
    apply hX₁Znot
    exact (ProjectionPerturbation.graph_adj_iff_blockers_eq_empty
      (ProjectionPerturbation.bbf P) K X₁ Z).mpr ⟨hX₁Z, hempty⟩
  obtain ⟨U₀, hU₀⟩ :
      ((ProjectionPerturbation.bbf P).blockers K X₁ Z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hblockers
  have hKhalf : K / 2 < K := by
    linarith [hK, P.ξ_pos]
  have hU₀half : U₀ ∈
      (ProjectionPerturbation.bbf P).blockers (K / 2) X₁ Z := by
    change U₀ ≠ X₁ ∧ U₀ ≠ Z ∧ K / 2 < P.bbfProjDist U₀ X₁ Z
    change U₀ ≠ X₁ ∧ U₀ ≠ Z ∧ K < P.bbfProjDist U₀ X₁ Z at hU₀
    exact ⟨hU₀.1, hU₀.2.1, hKhalf.trans hU₀.2.2⟩
  have hU₀before : 5 * P.ξ < P.bbfProjDist U₀ X₁ W := by
    have horder := hguard.2 X₁ hW₁12 U₀ hU₀
    rcases horder with hU₀W | hbefore
    · subst U₀
      exact (hW₁not hU₀half).elim
    · exact hbefore
  obtain ⟨W', hW'half, hW'before, hmax⟩ :=
    P.exists_maximal_half_blocker_before hK24 hW₁12
      ⟨U₀, hU₀half, hU₀before⟩
  have hW'W : W' ≠ W := P.ne_of_bbf_before hW'before
  have hend := P.bbfProjDist_endpoints_lt hW'half.1 hW'W
    hX₁W (by linarith [hW'before, P.ξ_pos])
  have htri := P.bbfProjDist_triangle hX₁W.symm hW'W.symm hW₀.2.1
    hW'half.1.symm hW'half.2.1 hX₁Z
  have hWW' : W ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) W' Z := by
    change W ≠ W' ∧ W ≠ Z ∧ 12 * P.ξ < P.bbfProjDist W W' Z
    refine ⟨hW'W.symm, hW₀.2.1, ?_⟩
    linarith [hW₁strong, hend.2, htri, hK, P.ξ_pos]
  have hW'12 : W' ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X₁ Z := by
    change W' ≠ X₁ ∧ W' ≠ Z ∧ 12 * P.ξ < P.bbfProjDist W' X₁ Z
    change W' ≠ X₁ ∧ W' ≠ Z ∧ K / 2 < P.bbfProjDist W' X₁ Z at hW'half
    exact ⟨hW'half.1, hW'half.2.1,
      lt_of_le_of_lt hhalf hW'half.2.2⟩
  have hguard' : IsBBFGuard P K W' Z := by
    refine ⟨⟨X₁, hW'12⟩, ?_⟩
    intro A hW'A V₀ hV₀
    have hAZ : A ≠ Z := P.ne_of_mem_bbf_blockers (by
      linarith [P.ξ_pos]) hW'A
    change W' ≠ A ∧ W' ≠ Z ∧
      12 * P.ξ < P.bbfProjDist W' A Z at hW'A
    change V₀ ≠ A ∧ V₀ ≠ Z ∧ K < P.bbfProjDist V₀ A Z at hV₀
    by_cases hV₀W' : V₀ = W'
    · exact Or.inl hV₀W'
    have hWA : W ≠ A := by
      intro hWA
      subst A
      have hend' := P.bbfProjDist_endpoints_lt hW'W hW'A.2.1
        hW₀.2.1 (by linarith [hW'A.2.2, P.ξ_pos])
      linarith [hWW'.2.2, hend'.1, P.ξ_pos]
    have hmono := P.bbfProjDist_right_mono hWA hW'W.symm hW₀.2.1
      hW'A.1 hW'A.2.1 hAZ (by linarith [hW'A.2.2, P.ξ_pos])
    rw [P.bbfProjDist_comm W Z W'] at hmono
    have hWA12 : W ∈
        (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) A Z :=
      ⟨hWA, hW₀.2.1, hWW'.2.2.trans_le hmono⟩
    have hV₀A12 : V₀ ∈
        (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) A Z :=
      ⟨hV₀.1, hV₀.2.1, lt_of_le_of_lt hK12 hV₀.2.2⟩
    have htotal := P.bbf_before_total_on_large (le_refl (12 * P.ξ))
      hW'A.1 hW'A.2.1 hV₀A12.1 hV₀A12.2.1
      (Ne.symm hV₀W') hW'A.2.2 hV₀A12.2.2
    rcases htotal with hW'V₀ | hV₀W'
    · have hV₀halfW' := P.mem_half_blockers_of_bbf_before
        (K := K) hK12 (by
          exact ⟨hW'A.1, hW'A.2.1, hW'A.2.2⟩) (by
          exact ⟨hV₀.1, hV₀.2.1, hV₀.2.2⟩) (Ne.symm hV₀W') hW'V₀
      have hV₀half := P.bbf_blocker_transfer_of_large
        (T := K / 2) (S := K / 2)
        (by linarith [hhalf, P.ξ_pos])
        (by linarith [hhalf, P.ξ_pos]) hW'half hV₀halfW'
      have hV₀W : V₀ ≠ W := by
        intro hV₀W
        subst V₀
        exact hW₁not hV₀half
      have hV₀beforeA : 5 * P.ξ < P.bbfProjDist V₀ A W := by
        have horder := hguard.2 A hWA12 V₀ (by
          exact ⟨hV₀.1, hV₀.2.1, hV₀.2.2⟩)
        exact horder.resolve_left hV₀W
      have hV₀12 : V₀ ∈
          (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X₁ Z :=
        ⟨hV₀half.1, hV₀half.2.1,
          lt_of_le_of_lt hhalf hV₀half.2.2⟩
      have hV₀before₁ := P.bbf_before_independent_of_left_endpoint
        (le_refl (12 * P.ξ)) hV₀A12 hWA12 hV₀12 hW₁12
          hV₀W hV₀beforeA
      have hmaxResult := hmax V₀ hV₀half hV₀before₁
      have hV₀beforeW'₁ := hmaxResult.resolve_left hV₀W'
      have hV₀beforeW'A := P.bbf_before_independent_of_left_endpoint
        (le_refl (12 * P.ξ)) hV₀12 hW'12 hV₀A12
          (by exact ⟨hW'A.1, hW'A.2.1, hW'A.2.2⟩)
          hV₀W' hV₀beforeW'₁
      exact (P.bbf_before_asymm hV₀A12.1 hV₀W' hW'A.1
        hV₀beforeW'A hW'V₀).elim
    · exact Or.inr hV₀W'
  exact ⟨W', hguard', hW'half, hWW'⟩

end ProjectionSystem
end GGT
end GroupApproximation
