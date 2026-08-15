import GroupApproximation.Monsters.P13Completeness

/-!
# The descent master induction and the completeness theorem

Work in progress: the step construction is being assembled from the
class rewrite lemmas; the master induction and the final assembly are
complete.  Nothing here is imported by the library root until the
step lands.
-/

namespace GroupApproximation
namespace P13DescentMaster

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13ColumnLift P13ParabolicKernel P13MonomialMachine
open P13DescentCore P13WordDescent P13Completeness

noncomputable section

/-- **One descent step.**  A word with a violation rewrites, up to a
signed-swap element pushed rightward, into a configuration of strictly
smaller measure. -/
theorem descent_step (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hviol : ∃ j, Viol V (act (toSL3 mon) e3) j) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  sorry

/-- **The descent normal form.**  Every word equals a norm-monotone
word times a signed-swap element. -/
theorem descent_normal_form (W : List Letter) :
    ∃ (G : List Letter) (mon : P13),
      mon ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      eval W = eval G * mon ∧ Mono G (act (toSL3 mon) e3) := by
  suffices H : ∀ p : ℕ × ℕ, ∀ (V : List Letter) (mon : P13),
      mon ∈ Subgroup.closure ({w13, w23} : Set P13) →
      meas V (act (toSL3 mon) e3) = p →
      ∃ (G : List Letter) (mon' : P13),
        mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
        eval V * mon = eval G * mon' ∧
        Mono G (act (toSL3 mon') e3) by
    obtain ⟨G, mon', h1, h2, h3⟩ :=
      H (meas W (act (toSL3 1) e3)) W 1 (Subgroup.one_mem _) rfl
    exact ⟨G, mon', h1, by simpa using h2, h3⟩
  intro p
  induction p using
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf).induction
    with
  | _ p IH =>
      intro V mon hmon hp
      by_cases hv : ∃ j, Viol V (act (toSL3 mon) e3) j
      · obtain ⟨V', mon', hmon', heval, hlt⟩ :=
          descent_step V mon hmon hv
        rw [hp] at hlt
        obtain ⟨G, mon'', h1, h2, h3⟩ :=
          IH _ hlt V' mon' hmon' rfl
        refine ⟨G, mon'', h1, ?_, h3⟩
        rw [← h2, heval]
      · push_neg at hv
        exact ⟨V, mon, hmon, rfl,
          (mono_iff_no_viol V _).mpr fun j hj => hv j hj⟩

/-- **Injectivity of the matrix model.** -/
theorem toSL3_injective : Function.Injective toSL3 := by
  rw [injective_iff_map_eq_one]
  exact toSL3_ker_eq_bot descent_normal_form

/-- **Completeness of the thirteen-relator presentation:** the
canonical homomorphism is an isomorphism `P13 ≃* SL₃(ℤ)`. -/
noncomputable def p13CompletenessEquiv : P13 ≃* SL3 :=
  MulEquiv.ofBijective toSL3
    ⟨toSL3_injective, SL3ElementaryGeneration.toSL3_surjective⟩

end

end P13DescentMaster
end GroupApproximation
