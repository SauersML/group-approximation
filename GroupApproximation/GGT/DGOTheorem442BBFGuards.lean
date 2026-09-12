import GroupApproximation.GGT.DGOTheorem442BBFMoveBound

/-!
# Guards and the BBF barrier inequality

This file begins the guards argument following Bestvina--Bromberg--Fujiwara
Lemma 3.18.  It proves the guard-constant estimate, independence of the large
projection order from the left endpoint, adjacency of a guard to its target,
and property (H) of BBF Theorem 3.3 with explicit constants.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- A BBF guard for `Z` at graph threshold `K`.  The first conjunct rules out
the vacuous case: the guard is a large projection from at least one viewpoint.
The second conjunct is the order condition in the definition preceding BBF
Lemma 3.18. -/
def IsBBFGuard (P : ProjectionSystem V) (K : ℝ) (W Z : V) : Prop :=
  (∃ X, W ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z) ∧
    ∀ X,
      W ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z →
      ∀ U,
        U ∈ (ProjectionPerturbation.bbf P).blockers K X Z →
        U = W ∨ 5 * P.ξ < P.bbfProjDist U X W

/-- The one-vertex projection system used to check that the guard predicate is
not made true by an empty family of viewpoints. -/
private def singletonProjectionSystem : ProjectionSystem PUnit where
  projDist := fun _ _ _ => 0
  ξ := 1
  ξ_pos := by norm_num
  nonneg := by intros; norm_num
  comm := by intros; rfl
  triangle := by intros; norm_num
  behrstock := by
    intro Y A B _ _ hAB
    exact (hAB (Subsingleton.elim A B)).elim
  finite_large := by
    intro A B hAB
    exact (hAB (Subsingleton.elim A B)).elim

/-- Model test for `IsBBFGuard`: the singleton system has no guard, since a
guard must occur as a genuine off-diagonal large projection. -/
theorem not_isBBFGuard_singletonModel (K : ℝ) (W Z : PUnit) :
    ¬ IsBBFGuard singletonProjectionSystem K W Z := by
  intro h
  obtain ⟨X, hWX⟩ := h.1
  change W ≠ X ∧ W ≠ Z ∧
    12 * singletonProjectionSystem.ξ <
      singletonProjectionSystem.bbfProjDist W X Z at hWX
  exact hWX.1 (Subsingleton.elim W X)

/-- The quantitative assertion of BBF's guard-constant lemma.  If `W` is a
`12ξ`-large projection of `(X,Z)`, `U` is `K`-large, and `W < U`, then
`U` is a `(K/2)`-large projection of `(W,Z)`. -/
theorem mem_half_blockers_of_bbf_before
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X Z W U : V}
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z)
    (hU : U ∈ (ProjectionPerturbation.bbf P).blockers K X Z)
    (hWU : W ≠ U)
    (hbefore : 5 * P.ξ < P.bbfProjDist W X U) :
    U ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) W Z := by
  have hXZ : X ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [P.ξ_pos]) hW
  change W ≠ X ∧ W ≠ Z ∧
    12 * P.ξ < P.bbfProjDist W X Z at hW
  change U ≠ X ∧ U ≠ Z ∧ K < P.bbfProjDist U X Z at hU
  have hend := P.bbfProjDist_endpoints_lt hW.1 hWU hU.1.symm (by
    linarith [hbefore, P.ξ_pos])
  have htri := P.bbfProjDist_triangle hU.1 hWU.symm hU.2.1
    hW.1.symm hW.2.1 hXZ
  refine ⟨hWU.symm, hU.2.1, ?_⟩
  change K / 2 < P.bbfProjDist U W Z
  linarith [hU.2.2, hend.2, hK, P.ξ_pos]

/-- The order of vertices which are large from two different left endpoints
is the same.  This is the endpoint-independence assertion used implicitly in
the nested-guards proof. -/
theorem bbf_before_independent_of_left_endpoint
    (P : ProjectionSystem V) {T : ℝ} (hT : 12 * P.ξ ≤ T)
    {X₀ X₁ Z U W : V}
    (hU₀ : U ∈ (ProjectionPerturbation.bbf P).blockers T X₀ Z)
    (hW₀ : W ∈ (ProjectionPerturbation.bbf P).blockers T X₀ Z)
    (hU₁ : U ∈ (ProjectionPerturbation.bbf P).blockers T X₁ Z)
    (hW₁ : W ∈ (ProjectionPerturbation.bbf P).blockers T X₁ Z)
    (hUW : U ≠ W)
    (hbefore : 5 * P.ξ < P.bbfProjDist U X₀ W) :
    5 * P.ξ < P.bbfProjDist U X₁ W := by
  have htotal := P.bbf_before_total_on_large hT
    hU₁.1 hU₁.2.1 hW₁.1 hW₁.2.1 hUW hU₁.2.2 hW₁.2.2
  rcases htotal with hresult | hreverse
  · exact hresult
  · have hsmall :=
      (P.bbf_before_consequences hT hU₀ hW₀ hUW hbefore).2.2
    have hlarge :=
      (P.bbf_before_consequences hT hW₁ hU₁ (Ne.symm hUW) hreverse).2.1
    linarith [hsmall, hlarge, hT, P.ξ_pos]

/-- The "in particular" clause of BBF's guard-constant lemma.  An empty
`K/2` blocker set from `W` to `Z`, together with one large viewpoint for `W`,
makes `W` a guard for `Z`. -/
theorem isBBFGuard_of_half_blockers_eq_empty
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {X₀ W Z : V}
    (hW₀ : W ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X₀ Z)
    (hempty : (ProjectionPerturbation.bbf P).blockers (K / 2) W Z = ∅) :
    IsBBFGuard P K W Z := by
  refine ⟨⟨X₀, hW₀⟩, ?_⟩
  intro X hW U hU
  by_cases hUW : U = W
  · exact Or.inl hUW
  have hU12 : U ∈
      (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z := by
    change U ≠ X ∧ U ≠ Z ∧ 12 * P.ξ < P.bbfProjDist U X Z
    change U ≠ X ∧ U ≠ Z ∧ K < P.bbfProjDist U X Z at hU
    exact ⟨hU.1, hU.2.1, lt_of_le_of_lt hK hU.2.2⟩
  have htotal := P.bbf_before_total_on_large (le_refl (12 * P.ξ))
    hW.1 hW.2.1 hU12.1 hU12.2.1 (Ne.symm hUW) hW.2.2 hU12.2.2
  rcases htotal with hWU | hUWbefore
  · have hhalf := P.mem_half_blockers_of_bbf_before hK hW hU
      (Ne.symm hUW) hWU
    rw [hempty] at hhalf
    exact hhalf.elim
  · exact Or.inr hUWbefore

/-- A nonvacuous guard is adjacent to its target in the projection graph.
This is the observation immediately after the definition of a guard. -/
theorem graph_adj_of_isBBFGuard
    (P : ProjectionSystem V) {K : ℝ} (hK : 12 * P.ξ ≤ K)
    {W Z : V} (hguard : IsBBFGuard P K W Z) :
    ((ProjectionPerturbation.bbf P).graph K).Adj W Z := by
  obtain ⟨X₀, hW₀⟩ := hguard.1
  have hXZ : X₀ ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [P.ξ_pos]) hW₀
  change W ≠ X₀ ∧ W ≠ Z ∧
    12 * P.ξ < P.bbfProjDist W X₀ Z at hW₀
  rw [ProjectionPerturbation.graph_adj_iff_blockers_eq_empty]
  refine ⟨hW₀.2.1, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro U hU
  change U ≠ W ∧ U ≠ Z ∧ K < P.bbfProjDist U W Z at hU
  have hUX : U ≠ X₀ := by
    intro hUX
    subst U
    have hend := P.bbfProjDist_endpoints_lt hW₀.1 hW₀.2.1 hXZ (by
      linarith [hW₀.2.2, P.ξ_pos])
    linarith [hU.2.2, hend.1, hK, P.ξ_pos]
  have hmono := P.bbfProjDist_right_mono hUX hU.1 hU.2.1
    hW₀.1 hW₀.2.1 hXZ (by linarith [hW₀.2.2, P.ξ_pos])
  rw [P.bbfProjDist_comm U Z W] at hmono
  have hU₀ : U ∈ (ProjectionPerturbation.bbf P).blockers K X₀ Z := by
    exact ⟨hUX, hU.2.1, hU.2.2.trans_le hmono⟩
  have horder := hguard.2 X₀ (by
    exact ⟨hW₀.1, hW₀.2.1, hW₀.2.2⟩) U hU₀
  rcases horder with hUW | hbefore
  · exact hU.1 hUW
  · have hU12 : U ∈
        (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X₀ Z :=
      ⟨hUX, hU.2.1, lt_of_le_of_lt hK hU₀.2.2⟩
    have hsmall :=
      (P.bbf_before_consequences (le_refl (12 * P.ξ)) hU12
        (by exact ⟨hW₀.1, hW₀.2.1, hW₀.2.2⟩) hU.1 hbefore).2.2
    linarith [hU.2.2, hsmall, hK, P.ξ_pos]

/-- Property (H) of BBF Theorem 3.3.  A vertex which is `T`-large from
both `(X₀,Z)` and `(X₁,Z)` forces the projection of `(X₀,X₁)` at `Z`
to be at most `T`. -/
theorem bbf_barrier_property
    (P : ProjectionSystem V) {T : ℝ} (hT : 12 * P.ξ ≤ T)
    {X₀ X₁ Z Y : V}
    (hY₀ : Y ∈ (ProjectionPerturbation.bbf P).blockers T X₀ Z)
    (hY₁ : Y ∈ (ProjectionPerturbation.bbf P).blockers T X₁ Z) :
    P.bbfProjDist Z X₀ X₁ ≤ T := by
  have hX₀Z : X₀ ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hT, P.ξ_pos]) hY₀
  have hX₁Z : X₁ ≠ Z := P.ne_of_mem_bbf_blockers (by
    linarith [hT, P.ξ_pos]) hY₁
  change Y ≠ X₀ ∧ Y ≠ Z ∧ T < P.bbfProjDist Y X₀ Z at hY₀
  change Y ≠ X₁ ∧ Y ≠ Z ∧ T < P.bbfProjDist Y X₁ Z at hY₁
  by_cases hX₀X₁ : X₀ = X₁
  · subst X₁
    rw [bbfProjDist, bbfRawProjDist,
      if_pos (Or.inr (Or.inr (Or.inl rfl)))]
    linarith [hT, P.ξ_pos]
  · by_contra hnot
    have hZlarge : T < P.bbfProjDist Z X₀ X₁ := lt_of_not_ge hnot
    have hYlarge : T < P.bbfProjDist Y X₀ X₁ := by
      have hmono := P.bbfProjDist_left_mono hY₀.1 hY₀.2.1 hY₁.1
        hX₀Z.symm hX₁Z.symm hX₀X₁ (by
          linarith [hZlarge, hT, P.ξ_pos])
      exact hY₀.2.2.trans_le hmono
    have htotal := P.bbf_before_total_on_large hT
      hX₀Z.symm hX₁Z.symm hY₀.1 hY₁.1 hY₀.2.1.symm
      hZlarge hYlarge
    let Q := ProjectionPerturbation.bbf P
    have hZblock : Z ∈ Q.blockers T X₀ X₁ :=
      ⟨hX₀Z.symm, hX₁Z.symm, hZlarge⟩
    have hYblock : Y ∈ Q.blockers T X₀ X₁ :=
      ⟨hY₀.1, hY₁.1, hYlarge⟩
    rcases htotal with hZY | hYZ
    · have hsmall :=
        (P.bbf_before_consequences hT hZblock hYblock
          hY₀.2.1.symm hZY).1
      linarith [hY₀.2.2, hsmall, hT, P.ξ_pos]
    · have hsmall :=
        (P.bbf_before_consequences hT hYblock hZblock
          hY₀.2.1 hYZ).2.2
      rw [P.bbfProjDist_comm Y Z X₁] at hsmall
      linarith [hY₁.2.2, hsmall, hT, P.ξ_pos]

end ProjectionSystem
end GGT
end GroupApproximation
