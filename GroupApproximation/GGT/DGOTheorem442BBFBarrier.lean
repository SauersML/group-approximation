import GroupApproximation.GGT.DGOTheorem442BBFNestedGuards

/-!
# BBF barriers and the distance-two bottleneck

This file proves the key barrier proposition in the guards subsection of
Bestvina--Bromberg--Fujiwara and applies property (H) to the standard walk.
At threshold `K ≥ 64ξ`, every walk between the standard endpoints passes
within graph distance two of every standard-walk vertex.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- If the current guard is `(K/2)`-large at `X`, then an initial guard which
is equal to it or nested above it is `12ξ`-large at `X`. -/
theorem initial_guard_mem_blockers_of_current
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {X Z W₀ W : V}
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z)
    (hrel : W₀ = W ∨
      W₀ ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) W Z) :
    W₀ ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) X Z := by
  have hhalf : 12 * P.ξ ≤ K / 2 := by
    calc
      12 * P.ξ ≤ 32 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K / 2 := by linarith [hK]
  rcases hrel with hW₀W | hW₀W
  · subst W₀
    change W ≠ X ∧ W ≠ Z ∧ 12 * P.ξ < P.bbfProjDist W X Z
    change W ≠ X ∧ W ≠ Z ∧ K / 2 < P.bbfProjDist W X Z at hW
    exact ⟨hW.1, hW.2.1, lt_of_le_of_lt hhalf hW.2.2⟩
  · exact P.bbf_blocker_transfer_of_large
      (T := K / 2) (S := 12 * P.ξ)
      (by linarith [hhalf, P.ξ_pos]) (by linarith [P.ξ_pos]) hW hW₀W

/-- Guard propagation along a chained vertex list.  The far hypotheses are
the graph-theoretic expansion of distance at least three from the target. -/
theorem initial_guard_is_barrier_along_isChain
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {Z X : V} {L : List V}
    (hchain : (X :: L).IsChain
      ((ProjectionPerturbation.bbf P).graph K).Adj)
    (hfar : ∀ A, A ∈ X :: L →
      A ≠ Z ∧
      ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A Z ∧
      ∀ W,
        ((ProjectionPerturbation.bbf P).graph K).Adj W Z →
        A ≠ W ∧ ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A W)
    {W₀ W : V}
    (hguard : IsBBFGuard P K W Z)
    (hW : W ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X Z)
    (hrel : W₀ = W ∨
      W₀ ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) W Z) :
    ∀ A, A ∈ X :: L →
      W₀ ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) A Z := by
  induction L generalizing X W with
  | nil =>
      intro A hA
      have hAX : A = X := by simpa using hA
      subst A
      exact P.initial_guard_mem_blockers_of_current hK hW hrel
  | cons X₁ L ih =>
      have h01 : ((ProjectionPerturbation.bbf P).graph K).Adj X X₁ :=
        hchain.rel
      have htail : (X₁ :: L).IsChain
          ((ProjectionPerturbation.bbf P).graph K).Adj := hchain.tail
      have hfarX := hfar X (by simp)
      have hfarX₁ := hfar X₁ (by simp)
      have hguardAdj := P.graph_adj_of_isBBFGuard (by
        calc
          12 * P.ξ ≤ 64 * P.ξ := by linarith [P.ξ_pos]
          _ ≤ K := hK) hguard
      have hbarrierX := P.initial_guard_mem_blockers_of_current hK hW hrel
      have hfarTail : ∀ A, A ∈ X₁ :: L →
          A ≠ Z ∧
          ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A Z ∧
          ∀ W',
            ((ProjectionPerturbation.bbf P).graph K).Adj W' Z →
            A ≠ W' ∧
              ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A W' := by
        intro A hA
        exact hfar A (by simp only [List.mem_cons]; exact Or.inr hA)
      by_cases hWnext :
          W ∈ (ProjectionPerturbation.bbf P).blockers (K / 2) X₁ Z
      · have htailBarrier := ih htail hfarTail hguard hWnext hrel
        intro A hA
        rcases List.mem_cons.mp hA with hAX | hAtail
        · subst A
          exact hbarrierX
        · exact htailBarrier A hAtail
      · obtain ⟨W', hguard', hW'next, hWW'⟩ :=
          P.exists_nested_isBBFGuard hK h01 hguard hW hWnext
            (hfarX.2.2 W hguardAdj).2
            (hfarX₁.2.2 W hguardAdj).1 hfarX₁.1 hfarX₁.2.1
        have hrel' : W₀ = W' ∨
            W₀ ∈ (ProjectionPerturbation.bbf P).blockers
              (12 * P.ξ) W' Z := by
          rcases hrel with hW₀W | hW₀W
          · right
            simpa only [hW₀W] using hWW'
          · right
            exact P.bbf_blocker_transfer_of_large
              (T := 12 * P.ξ) (S := 12 * P.ξ)
              (by linarith [P.ξ_pos]) (by linarith [P.ξ_pos]) hWW' hW₀W
        have htailBarrier := ih htail hfarTail hguard' hW'next hrel'
        intro A hA
        rcases List.mem_cons.mp hA with hAX | hAtail
        · subst A
          exact hbarrierX
        · exact htailBarrier A hAtail

/-- **BBF key barrier proposition.**  If every vertex of a walk stays at
graph distance at least three from `Z` (expanded into one- and two-edge
conditions), one vertex is a `12ξ`-large projection of `(A,Z)` for every
vertex `A` of the walk. -/
theorem exists_bbf_barrier_for_walk
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {X Y Z : V}
    (p : ((ProjectionPerturbation.bbf P).graph K).Walk X Y)
    (hfar : ∀ A, A ∈ p.support →
      A ≠ Z ∧
      ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A Z ∧
      ∀ W,
        ((ProjectionPerturbation.bbf P).graph K).Adj W Z →
        A ≠ W ∧ ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A W) :
    ∃ W, ∀ A, A ∈ p.support →
      W ∈ (ProjectionPerturbation.bbf P).blockers (12 * P.ξ) A Z := by
  have hfarX := hfar X p.start_mem_support
  obtain ⟨W, hguard, hWhalf⟩ :=
    P.exists_isBBFGuard_mem_half_blockers_of_not_adj hK
      hfarX.1 hfarX.2.1
  refine ⟨W, ?_⟩
  exact P.initial_guard_is_barrier_along_isChain hK
    p.isChain_adj_support hfar hguard hWhalf (Or.inl rfl)

/-- **BBF distance-two bottleneck theorem.**  There is a standard walk from
`X` to `Z` such that every competing walk from `X` to `Z` passes within graph
distance two of every vertex in the standard support.  This is the conclusion
used in the proof of BBF Theorem 3.16. -/
theorem exists_bbf_standard_walk_within_two
    (P : ProjectionSystem V) {K : ℝ} (hK : 64 * P.ξ ≤ K)
    {X Z : V} (hXZ : X ≠ Z) :
    ∃ standard : ((ProjectionPerturbation.bbf P).graph K).Walk X Z,
      ∀ competing : ((ProjectionPerturbation.bbf P).graph K).Walk X Z,
        ∀ Y, Y ∈ standard.support →
          ∃ W, W ∈ competing.support ∧
            ((ProjectionPerturbation.bbf P).graph K).dist Y W ≤ 2 := by
  have hK12 : 12 * P.ξ ≤ K := by
    calc
      12 * P.ξ ≤ 64 * P.ξ := by linarith [P.ξ_pos]
      _ ≤ K := hK
  obtain ⟨L, _hnodup, hmem, _hpair, standard, hsupport⟩ :=
    P.exists_bbf_standard_walk hK12 hXZ
  refine ⟨standard, ?_⟩
  intro competing Y hY
  rw [hsupport] at hY
  simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hY
  rcases hY with hYX | hYL | hYZ
  · subst Y
    exact ⟨X, competing.start_mem_support, by simp⟩
  · have hYlarge := (hmem Y).mp hYL
    by_contra hnone
    push_neg at hnone
    have hfar : ∀ A, A ∈ competing.support →
        A ≠ Y ∧
        ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A Y ∧
        ∀ W,
          ((ProjectionPerturbation.bbf P).graph K).Adj W Y →
          A ≠ W ∧
            ¬ ((ProjectionPerturbation.bbf P).graph K).Adj A W := by
      intro A hA
      have hdist := hnone A hA
      refine ⟨?_, ?_, ?_⟩
      · intro hAY
        subst A
        exact hdist (by simp)
      · intro hAY
        have hdistOne :
            ((ProjectionPerturbation.bbf P).graph K).dist Y A = 1 :=
          SimpleGraph.dist_eq_one_iff_adj.mpr hAY.symm
        exact hdist (by omega)
      · intro W hWY
        constructor
        · intro hAW
          subst A
          have hdistOne :
              ((ProjectionPerturbation.bbf P).graph K).dist Y W = 1 :=
            SimpleGraph.dist_eq_one_iff_adj.mpr hWY.symm
          exact hdist (by omega)
        · intro hAW
          have q : ((ProjectionPerturbation.bbf P).graph K).Walk Y A :=
            hWY.symm.toWalk.append hAW.symm.toWalk
          have hle := SimpleGraph.dist_le q
          have hq : q.length = 2 := by simp [q]
          exact hdist (by omega)
    obtain ⟨B, hbarrier⟩ := P.exists_bbf_barrier_for_walk hK competing hfar
    have hBX := hbarrier X competing.start_mem_support
    have hBZ := hbarrier Z competing.end_mem_support
    have hsmall := P.bbf_barrier_property (le_refl (12 * P.ξ)) hBX hBZ
    change Y ≠ X ∧ Y ≠ Z ∧ K < P.bbfProjDist Y X Z at hYlarge
    linarith [hYlarge.2.2, hsmall, hK12]
  · subst Y
    exact ⟨Z, competing.end_mem_support, by simp⟩

end ProjectionSystem
end GGT
end GroupApproximation
