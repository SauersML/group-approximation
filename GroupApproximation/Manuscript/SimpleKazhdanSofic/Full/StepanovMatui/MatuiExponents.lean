import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiReturns
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Exponents of an eight-level tower

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  For an infinite minimal system, a point `x` and a nonempty open set `V`:

* `exists_injective_returns`: there are `k` distinct return times of `x` into `V`, all outside a
  given finite set;
* `exists_eight_exponents`: for distinct nonzero `a, c` there are distinct exponents
  `0, a, c, m₀, …, m₄` whose last five are return times of `x` into `V`.
-/

variable {X : Type*}

/-- **Distinct returns** of a minimal orbit into an open set, avoiding a finite set. -/
theorem exists_injective_returns [TopologicalSpace X] [CompactSpace X] [T2Space X] [Infinite X]
    (T : X ≃ₜ X) (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {V : Set X} (hV : IsOpen V)
    (hVne : V.Nonempty) (x : X) (F : Finset ℤ) (k : ℕ) :
    ∃ m : Fin k → ℤ, Function.Injective m ∧ (∀ i, m i ∉ F) ∧ ∀ i, (T ^ m i) x ∈ V := by
  induction k generalizing F with
  | zero =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨m₀, hm₀F, hm₀V⟩ := exists_zpow_mem_notMem T hmin hV hVne x F
    obtain ⟨m, hinj, hmF, hmV⟩ := ih (insert m₀ F)
    refine ⟨Fin.cons m₀ m, Fin.cons_injective_of_injective ?_ hinj, fun i => ?_, fun i => ?_⟩
    · rintro ⟨j, hj⟩
      apply hmF j
      rw [hj]
      exact Finset.mem_insert_self m₀ F
    · induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hm₀F
      | succ j =>
        rw [Fin.cons_succ]
        exact fun h => hmF j (Finset.mem_insert_of_mem h)
    · induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hm₀V
      | succ j =>
        rw [Fin.cons_succ]
        exact hmV j

/-- **Exponents of the eight-level tower**: `0, a, c` and five distinct returns into `V`. -/
theorem exists_eight_exponents [TopologicalSpace X] [CompactSpace X] [T2Space X] [Infinite X]
    (T : X ≃ₜ X) (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {V : Set X} (hV : IsOpen V)
    (hVne : V.Nonempty) (x : X) {a c : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) (hac : a ≠ c) :
    ∃ E : Fin 8 → ℤ, ∃ m : Fin 5 → ℤ, E 0 = 0 ∧ E 1 = a ∧ E 2 = c ∧ Function.Injective E ∧
      (∀ j, (T ^ m j) x ∈ V) ∧ ∀ i : Fin 8, 3 ≤ (i : ℕ) → ∃ j, E i = m j := by
  obtain ⟨m, hinj, hmF, hmV⟩ := exists_injective_returns T hmin hV hVne x {0, a, c} 5
  have h0F : (0 : ℤ) ∈ ({0, a, c} : Finset ℤ) := Finset.mem_insert_self 0 _
  have haF : a ∈ ({0, a, c} : Finset ℤ) := Finset.mem_insert_of_mem (Finset.mem_insert_self a _)
  have hcF : c ∈ ({0, a, c} : Finset ℤ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
  have hinj2 : Function.Injective (Fin.cons c m : Fin 6 → ℤ) := by
    refine Fin.cons_injective_of_injective ?_ hinj
    rintro ⟨j, hj⟩
    apply hmF j
    rw [hj]
    exact hcF
  have hinj1 : Function.Injective (Fin.cons a (Fin.cons c m) : Fin 7 → ℤ) := by
    refine Fin.cons_injective_of_injective ?_ hinj2
    rintro ⟨j, hj⟩
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero] at hj
      exact hac hj.symm
    | succ j =>
      rw [Fin.cons_succ] at hj
      apply hmF j
      rw [hj]
      exact haF
  have hinj0 : Function.Injective (Fin.cons 0 (Fin.cons a (Fin.cons c m)) : Fin 8 → ℤ) := by
    refine Fin.cons_injective_of_injective ?_ hinj1
    rintro ⟨j, hj⟩
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero] at hj
      exact ha hj
    | succ j =>
      induction j using Fin.cases with
      | zero =>
        rw [Fin.cons_succ, Fin.cons_zero] at hj
        exact hc hj
      | succ j =>
        rw [Fin.cons_succ, Fin.cons_succ] at hj
        apply hmF j
        rw [hj]
        exact h0F
  refine ⟨Fin.cons 0 (Fin.cons a (Fin.cons c m)), m, rfl, rfl, rfl, hinj0, hmV, fun i hi => ?_⟩
  induction i using Fin.cases with
  | zero => exact absurd hi (by decide)
  | succ i =>
    induction i using Fin.cases with
    | zero => exact absurd hi (by decide)
    | succ i =>
      induction i using Fin.cases with
      | zero => exact absurd hi (by decide)
      | succ j =>
        refine ⟨j, ?_⟩
        rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_injective_returns
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_eight_exponents
