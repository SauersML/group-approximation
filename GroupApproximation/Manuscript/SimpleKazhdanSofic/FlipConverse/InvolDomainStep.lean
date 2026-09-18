import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution normal form, part 1: the greedy step

Lane sk-flip-11 (Bezuglyi–Medynets involution normal form), census row `2e7c7d9ab149`
(tex: "for topological full groups the converse holds"; absent from current tex).

Let `σ` be a homeomorphism with `σ (σ z) = z` for all `z`. Suppose `U : X → Set X` is a family of
clopen sets, each *displaced* by `σ` (`z ∈ U x → σ z ∉ U x`). Then for every finite set `t` of
indices there is a clopen `V` displaced by `σ` whose saturation `V ∪ σ⁻¹ V` contains every `U x`
with `x ∈ t`.

Proof: induction on `t`. Start with `V = ∅`. To add `U a`, put
`V' := V ∪ (U a \ (V ∪ σ⁻¹ V))`. The set `V'` is clopen, and it is displaced because:
* `V` is displaced;
* `σ` swaps `V` and `σ⁻¹ V` (so `z ∈ V` and `σ z ∈ U a \ σ⁻¹ V` are incompatible);
* `U a` is displaced.
Every point of `U a` lies in `V`, in `σ⁻¹ V`, or in the new piece.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The greedy fundamental-domain step for an involutive homeomorphism and a finite family of
displaced clopen sets. -/
theorem exists_displaced_clopen_saturating_finset {σ : X ≃ₜ X} (hs : ∀ z, σ (σ z) = z)
    {U : X → Set X} (hUc : ∀ x, IsClopen (U x)) (hUd : ∀ x, ∀ z ∈ U x, σ z ∉ U x)
    (t : Finset X) :
    ∃ V : Set X, IsClopen V ∧ (∀ z ∈ V, σ z ∉ V) ∧ ∀ x ∈ t, U x ⊆ V ∪ σ ⁻¹' V := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨∅, isClopen_empty, fun z hz => absurd hz (Set.notMem_empty z), ?_⟩
    intro x hx
    exact absurd hx (Finset.notMem_empty x)
  | insert a t _ ih =>
    obtain ⟨V, hVc, hVd, hVU⟩ := ih
    refine ⟨V ∪ (U a \ (V ∪ σ ⁻¹' V)),
      hVc.union ((hUc a).diff (hVc.union (hVc.preimage σ.continuous))), ?_, ?_⟩
    · intro z hz hz'
      rcases (Set.mem_union _ _ _).1 hz with hzV | hzN
      · rcases (Set.mem_union _ _ _).1 hz' with hszV | hszN
        · exact hVd z hzV hszV
        · have hnot : σ z ∉ V ∪ σ ⁻¹' V := ((Set.mem_diff _).1 hszN).2
          have hssz : σ (σ z) ∈ V := by
            rw [hs z]
            exact hzV
          exact hnot ((Set.mem_union _ _ _).2 (Or.inr hssz))
      · have hzUa : z ∈ U a := ((Set.mem_diff _).1 hzN).1
        have hznot : z ∉ V ∪ σ ⁻¹' V := ((Set.mem_diff _).1 hzN).2
        rcases (Set.mem_union _ _ _).1 hz' with hszV | hszN
        · exact hznot ((Set.mem_union _ _ _).2 (Or.inr hszV))
        · exact hUd a z hzUa ((Set.mem_diff _).1 hszN).1
    · intro x hx
      rcases Finset.mem_insert.1 hx with hxa | hxt
      · rw [hxa]
        intro z hz
        by_cases hzS : z ∈ V ∪ σ ⁻¹' V
        · rcases (Set.mem_union _ _ _).1 hzS with hzV | hszV
          · exact (Set.mem_union _ _ _).2 (Or.inl ((Set.mem_union _ _ _).2 (Or.inl hzV)))
          · have h : σ z ∈ V ∪ (U a \ (V ∪ σ ⁻¹' V)) := (Set.mem_union _ _ _).2 (Or.inl hszV)
            exact (Set.mem_union _ _ _).2 (Or.inr h)
        · exact (Set.mem_union _ _ _).2
            (Or.inl ((Set.mem_union _ _ _).2 (Or.inr ((Set.mem_diff _).2 ⟨hz, hzS⟩))))
      · intro z hz
        rcases (Set.mem_union _ _ _).1 (hVU x hxt hz) with hzV | hszV
        · exact (Set.mem_union _ _ _).2 (Or.inl ((Set.mem_union _ _ _).2 (Or.inl hzV)))
        · have h : σ z ∈ V ∪ (U a \ (V ∪ σ ⁻¹' V)) := (Set.mem_union _ _ _).2 (Or.inl hszV)
          exact (Set.mem_union _ _ _).2 (Or.inr h)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_displaced_clopen_saturating_finset
