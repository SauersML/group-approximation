import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteAll
import GroupApproximation.Meta.AxiomGuard

/-!
# Transferring the all-swaps presentation to the short quotient (lane bh-met-77b)

`higmanVC_Q d` is the quotient of the short free group by the normal closure of
`higmanVFPRelators d`.  Given values `τ` for the generators of the all-swaps free group, the
homomorphism `higmanVC_psi d τ` sends a short pair `(v, w)` to the class of its letter and any
other pair `p` to `τ p`.  Then:

* `higmanVC_psi_comp_iota`: `ψ_τ ∘ ι` is the quotient map, for every `τ`;
* `higmanVC_psi_short`: `ψ_τ` kills every standard relator all of whose words have length
  `≤ 3`, for every `τ` (these are the letter relators of lane bh-met-77).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The short free group modulo the normal closure of the length-bounded relators. -/
abbrev higmanVC_Q (d : ℕ) : Type :=
  FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) ⧸
    Subgroup.normalClosure (higmanVFPRelators d)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_Q

/-- The quotient map onto `higmanVC_Q d`. -/
noncomputable def higmanVC_mk (d : ℕ) :
    FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) →* higmanVC_Q d :=
  QuotientGroup.mk' (Subgroup.normalClosure (higmanVFPRelators d))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_mk

/-- Relators are killed by the quotient map. -/
theorem higmanVC_mk_rel {d : ℕ} {r : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))}
    (hr : r ∈ higmanVFPRelators d) : higmanVC_mk d r = 1 := by
  rw [higmanVC_mk, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact Subgroup.subset_normalClosure hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_mk_rel

/-- An element killed by the quotient map lies in the normal closure. -/
theorem higmanVC_mem_of_mk {d : ℕ} {r : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))}
    (hr : higmanVC_mk d r = 1) : r ∈ Subgroup.normalClosure (higmanVFPRelators d) := by
  rw [higmanVC_mk, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hr
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_mem_of_mk

/-- The value of `ψ_τ` on a generator: the class of the letter for short pairs, else `τ p`. -/
noncomputable def higmanVC_psiGen (d : ℕ) (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    (p : List (Fin d) × List (Fin d)) : higmanVC_Q d :=
  if h : p.1.length ≤ 3 ∧ p.2.length ≤ 3 then higmanVC_mk d (higmanVFPLetter h.1 h.2) else τ p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psiGen

/-- The homomorphism `ψ_τ` from the all-swaps free group to `higmanVC_Q d`. -/
noncomputable def higmanVC_psi (d : ℕ) (τ : List (Fin d) × List (Fin d) → higmanVC_Q d) :
    FreeGroup (List (Fin d) × List (Fin d)) →* higmanVC_Q d :=
  FreeGroup.lift (higmanVC_psiGen d τ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi

/-- `ψ_τ` on a short generator `p`. -/
theorem higmanVC_psi_of_pair {d : ℕ} (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    (p : List (Fin d) × List (Fin d)) (hv : p.1.length ≤ 3) (hw : p.2.length ≤ 3) :
    higmanVC_psi d τ (FreeGroup.of p) = higmanVC_mk d (higmanVFPLetter hv hw) := by
  rw [higmanVC_psi, FreeGroup.lift_apply_of, higmanVC_psiGen]
  exact dif_pos (And.intro hv hw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi_of_pair

/-- `ψ_τ` on a short generator `(v, w)`. -/
theorem higmanVC_psi_of_short {d : ℕ} (τ : List (Fin d) × List (Fin d) → higmanVC_Q d)
    {v w : List (Fin d)} (hv : v.length ≤ 3) (hw : w.length ≤ 3) :
    higmanVC_psi d τ (FreeGroup.of (v, w)) = higmanVC_mk d (higmanVFPLetter hv hw) := by
  rw [higmanVC_psi, FreeGroup.lift_apply_of, higmanVC_psiGen]
  exact dif_pos (And.intro hv hw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi_of_short

/-- The first word of an enumerated short pair has length `≤ 3`. -/
theorem higmanVC_short_fst (d : ℕ) (i : Fin (Nat.card ↥(vgenShortPairs (Fin d)))) :
    ((vgenShortEquiv (Fin d)).symm i).1.1.length ≤ 3 :=
  (Set.mem_prod (s := {l : List (Fin d) | l.length ≤ 3}) (t := {l : List (Fin d) | l.length ≤ 3})
    |>.mp ((vgenShortEquiv (Fin d)).symm i).2).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_short_fst

/-- The second word of an enumerated short pair has length `≤ 3`. -/
theorem higmanVC_short_snd (d : ℕ) (i : Fin (Nat.card ↥(vgenShortPairs (Fin d)))) :
    ((vgenShortEquiv (Fin d)).symm i).1.2.length ≤ 3 :=
  (Set.mem_prod (s := {l : List (Fin d) | l.length ≤ 3}) (t := {l : List (Fin d) | l.length ≤ 3})
    |>.mp ((vgenShortEquiv (Fin d)).symm i).2).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_short_snd

/-- The letter of the `i`-th enumerated short pair is the `i`-th free generator. -/
theorem higmanVC_letter_symm (d : ℕ) (i : Fin (Nat.card ↥(vgenShortPairs (Fin d))))
    (hv : ((vgenShortEquiv (Fin d)).symm i).1.1.length ≤ 3)
    (hw : ((vgenShortEquiv (Fin d)).symm i).1.2.length ≤ 3) :
    higmanVFPLetter hv hw = FreeGroup.of i := by
  unfold higmanVFPLetter
  exact congrArg FreeGroup.of ((Equiv.apply_eq_iff_eq_symm_apply _).mpr (Subtype.ext rfl))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_letter_symm

/-- **`ψ_τ ∘ ι` is the quotient map**, for every `τ`. -/
theorem higmanVC_psi_comp_iota (d : ℕ) (τ : List (Fin d) × List (Fin d) → higmanVC_Q d) :
    (higmanVC_psi d τ).comp (higmanVC_iota d) = higmanVC_mk d := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, higmanVC_iota, FreeGroup.lift_apply_of,
    higmanVC_psi_of_pair τ ((vgenShortEquiv (Fin d)).symm i).1 (higmanVC_short_fst d i)
      (higmanVC_short_snd d i), higmanVC_letter_symm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVC_psi_comp_iota

end GroupApproximation.BooneHigman.Metabelian.Envelope
