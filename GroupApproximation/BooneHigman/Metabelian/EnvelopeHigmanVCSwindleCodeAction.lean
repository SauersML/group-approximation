import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleSupport
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpTree
import GroupApproximation.Meta.AxiomGuard

/-!
# Code-shuffle action under leaf expansion

An elementary shuffle updates a lift of the code table `c a ↦ a c` after
expanding one leaf. Every finite expansion tree consequently has such a lift.
Existence alone does not give a canonical lift or independence of expansion
history; the exact coherence theorem remains a separate obligation.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A quotient element lifts the code table that moves the last letter first. -/
def higSw_codeAction {d : ℕ} (C : Finset (List (Fin d)))
    (q : higmanVCCommon_Q d) : Prop :=
  ∀ c ∈ C, ∀ a : Fin d,
    MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d)))
      (c ++ [a]) ([a] ++ c)

theorem higSw_codeAction_root (d : ℕ) :
    higSw_codeAction ({[]} : Finset (List (Fin d))) 1 := by
  intro c hc a
  have hc' : c = [] := Finset.mem_singleton.mp hc
  subst c
  simpa only [map_one, Subgroup.coe_one, List.nil_append, List.append_nil] using
    mapsCone_one ([a] : List (Fin d))

/-- The actual quotient product has the expanded code action. -/
theorem higSw_codeAction_expand {d : ℕ} {C : Finset (List (Fin d))}
    {c : List (Fin d)} {q : higmanVCCommon_Q d}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hc : c ∈ C) (hq : higSw_codeAction C q) :
    higSw_codeAction (higmanVCLeafExp_expand C c) (higSw_shuffle d c * q) := by
  intro e he a
  simp only [map_mul, Subgroup.coe_mul]
  rcases higmanVCLeafExp_mem_expand.mp he with ⟨hec, heC⟩ | ⟨b, rfl⟩
  · exact (hq e heC a).comp
      (higSw_shuffle_fix (hC c hc e heC (Ne.symm hec)) (hC e heC c hc hec) a)
  · simpa only [List.append_assoc] using
      ((hq c hc b).append [a]).comp (higSw_shuffle_mapsCone c b a)

/-- Existence of a code-shuffle lift for every finite leaf-expansion tree. -/
theorem higSw_codeAction_exists {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCLeafExp_IsTree C) :
    ∃ q : higmanVCCommon_Q d, higSw_codeAction C q := by
  induction hC with
  | root => exact ⟨1, higSw_codeAction_root d⟩
  | @expand C c hC hc ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨higSw_shuffle d c * q,
      higSw_codeAction_expand (higmanVCLeafExp_tree_isAC hC) hc hq⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeAction_expand
#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_codeAction_exists

end GroupApproximation.BooneHigman.Metabelian.Envelope
