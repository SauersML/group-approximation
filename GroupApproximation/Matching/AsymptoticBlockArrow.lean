import GroupApproximation.Matching.AsymptoticPartialGroupoid
import GroupApproximation.Matching.BlockPartialBijection

/-!
# Asymptotic arrows between expander components

An exact inverse pair of model permutations transports every reciprocal
sequence of component blocks by a co-negligible partial bijection.  The source
defect is the forward component leakage and the target defect is the reverse
component leakage.  Both are squeezed by their global leakage sums.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- A choice of one component at every approximation level. -/
abbrev ComponentSequence := ∀ n, D.componentIndex n

/-- The finite model carried by a component sequence. -/
abbrev componentSequenceModel (C : D.ComponentSequence) (n : ℕ) : FiniteModel :=
  indexedBlockModel (D.blocks n) (C n)

/-- Pointwise chosen target sequence of a permutation sequence. -/
noncomputable def refineSequence
    (q : ∀ n, Equiv.Perm (S.model n)) (C : D.ComponentSequence) :
    D.ComponentSequence := fun n ↦ D.refineIndex (q n) (C n)

/-- A reciprocal component sequence supplies an actual asymptotic partial
bijection between the source components and their chosen targets. -/
noncomputable def refinementAsymptoticPartialBijection
    (q r : ∀ n, Equiv.Perm (S.model n))
    (hr : ∀ n, r n = (q n)⁻¹)
    (hqLeak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ)))
    (hrLeak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (r n) C : ℝ)))
    (C : D.ComponentSequence)
    (hrecip : ∀ n, D.refineIndex (r n) (D.refineIndex (q n) (C n)) = C n) :
    AsymptoticPartialBijection
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      (D.componentSequenceModel C)
      (D.componentSequenceModel (D.refineSequence q C)) where
  map n := D.refinementPartialBijection (q n) (C n)
  source_negligible := by
    apply Negligible.mono_nonneg (fun _ ↦ by positivity)
      (fun _ ↦ by positivity) (fun n ↦ ?_) hqLeak
    change ((D.refinementPartialBijection (q n) (C n)).sourceDefect : ℝ) ≤
      ∑ E : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) E : ℝ)
    rw [D.refinementPartialBijection_sourceDefect]
    exact_mod_cast Finset.single_le_sum
      (fun C _ ↦ by positivity : ∀ C : D.componentIndex n, C ∈ Finset.univ →
        0 ≤ (D.componentLeakage (D.blocks n) (q n) C : ℝ))
      (Finset.mem_univ (C n))
  target_negligible := by
    apply Negligible.mono_nonneg (fun _ ↦ by positivity)
      (fun _ ↦ by positivity) (fun n ↦ ?_) hrLeak
    change ((D.refinementPartialBijection (q n) (C n)).targetDefect : ℝ) ≤
      ∑ E : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (r n) E : ℝ)
    rw [D.refinementPartialBijection_targetDefect_of_inverse
      (q n) (r n) (hr n) (C n) (hrecip n)]
    exact_mod_cast Finset.single_le_sum
      (fun E _ ↦ by positivity : ∀ E : D.componentIndex n, E ∈ Finset.univ →
        0 ≤ (D.componentLeakage (D.blocks n) (r n) E : ℝ))
      (Finset.mem_univ (D.refineIndex (q n) (C n)))

end ExpanderDecomposition
end GroupApproximation
