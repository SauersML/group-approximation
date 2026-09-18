import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStabilityPropagate
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStabilityDescend
import GroupApproximation.Meta.AxiomGuard

/-!
# Stability from rank five reduces to the single step `K₂(5) → K₂(6)` (sk-leavitt-28, part 4)

Write `L = L_{𝔽₂}(1,2)`.  The target `BinaryLeavittK2FiveStabilityStatement` says: an element of
`K₂(5, L)` that dies in some `St_N(L)` is trivial.  This module reduces it to the one-step
statement `BinaryLeavittK2FiveStepStatement`: an element of `K₂(5, L)` that dies in `St_6(L)` is
trivial.

## The reduction (`binaryLeavittK2FiveStability_of_step`)

1. The step makes `K₂(5, L)` central (`fiveStability_K2_le_center_of_k2StabInjective`).
2. Centrality climbs along the Leavitt refinement, so `K₂(m, L)` is central for every `m ≥ 5`
   (`fiveStability_K2_le_center_succ`).
3. With `K₂(M + 1)` central, the refinement of the last index is injective and turns padding into
   padding (`fiveStability_descend`).  So a death in `St_N(L)` descends to a death in `St_6(L)`.
4. The step finishes.

## Truth check

`K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4) gives the step at once
(`binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective`).  So the step is true.

## Size of the step (honest accounting)

The step is **logically equivalent** to the target: `binaryLeavittK2FiveStep_of_fiveStability`
proves the converse in one line.  No sufficient statement implied by a true target can be
logically weaker, so the gain is in proof content only.  The step fixes both ranks (`St_5 → St_6`),
where the target quantifies over every `N ≥ 5`.  The whole telescoping and descent argument is
proved here in Lean, using the Kervaire lift, Khanh's Lemma 5.2 and the Leavitt refinement.

## Loud negative finding: the retraction route is false

A homomorphism `ρ : St_N(L) → St_5(L)` with `ρ ∘ pad = (inner automorphism)` does **not** exist
for `N ≥ 6`, not even up to `K₂`.  Choose `λ ∈ L` with `λ ≠ 0, 1` in the center-free sense and let
`y` lift `diag(1_5, λ, 1, …)` in `E_N(L)`.  Then `y` commutes with `pad(St_5)` modulo `K₂`, so
`proj ∘ ρ` kills the normal closure of a non-central element of the simple group `E_N(L)`.  That
forces `proj ∘ ρ = 1`, which contradicts `proj ∘ ρ ∘ pad = (inner automorphism of E_5)`.  The route
internal to `L` that works is the refinement descent above, not a retraction.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- **The one-step stability statement** over `L_{𝔽₂}(1,2)`: padding `K₂(5, L) → K₂(6, L)` is
injective.

*Why it is true.*  `K₂(5, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.4); see
`binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective`.  Not proved in Lean. -/
def BinaryLeavittK2FiveStepStatement : Prop :=
  Full.LVH2GL3.K2StabInjective (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) 5

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittK2FiveStepStatement

/-- **Stability from rank five from the single step `K₂(5) → K₂(6)`.**  The step makes `K₂(5)`
central.  Centrality climbs to every rank `m ≥ 5`, so a death in `St_N(L)` descends to `St_6(L)`,
where the step applies. -/
theorem binaryLeavittK2FiveStability_of_step (hS : BinaryLeavittK2FiveStepStatement) :
    BinaryLeavittK2FiveStabilityStatement := by
  have hC : ∀ m : ℕ, 5 ≤ m →
      BooneHigman.SteinbergBasic.K2 (Fin m) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
        Subgroup.center (SteinbergGroup (Fin m) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fiveStability_K2_le_center_of_k2StabInjective hS
    | succ m hm ih =>
      exact fiveStability_K2_le_center_succ (BinaryLeavitt.family (ZMod 2))
        (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩
        (fun e => by
          have h1 : (1 : ℕ) = 0 := congrArg Fin.val e
          omega) ih
  have hdesc : ∀ (M : ℕ) (hM : 5 ≤ M)
      (k : SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))),
      indexMap (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
          (Fin.castLEEmb (show 5 ≤ M + 1 by omega)) k = 1 →
        indexMap (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
          (Fin.castLEEmb (Nat.le_succ 5)) k = 1 := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      intro k hk
      exact hk
    | succ M hM ih =>
      intro k hk
      exact ih k (fiveStability_descend (BinaryLeavitt.family (ZMod 2)) (by omega) hM
        (hC (M + 1) (by omega)) hk)
  intro k hk N hN hk1
  by_cases hN5 : N = 5
  · subst hN5
    exact (Full.LVH2GL3.indexMap_castLEEmb_self hN k).symm.trans hk1
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact hS k ((BooneHigman.SteinbergBasic.mem_K2_iff k).mp hk) (hdesc M (by omega) k hk1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStability_of_step

/-- The converse: the target gives the step.  This records that the step is logically equivalent
to the target and smaller only in proof content (two fixed ranks instead of all `N`). -/
theorem binaryLeavittK2FiveStep_of_fiveStability (hT : BinaryLeavittK2FiveStabilityStatement) :
    BinaryLeavittK2FiveStepStatement :=
  k2StabInjective_of_binaryLeavittK2FiveStability hT 5 (Nat.le_refl 5)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStep_of_fiveStability

/-- **Truth check.**  `K₂(5, L) = ⊥` gives the step trivially. -/
theorem binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective
    (h : LeavittFP.BinaryLeavittSteinbergInjectiveStatement) :
    BinaryLeavittK2FiveStepStatement := by
  have h5 : (projection (I := Fin 5) (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).ker =
      ⊥ := h
  exact Full.LVH2GL3.k2StabInjective_of_ker_eq_bot h5

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStep_of_binaryLeavittSteinbergInjective

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
