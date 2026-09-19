import GroupApproximation.Sofic.NormMFCoronaRadical

/-!
# Radical pullback through a defect quotient

**Section 36.5** of the dossier.  If a normal subgroup already lies inside the
MF radical, then the radical is exactly the preimage of the radical of the
quotient.  Two consequences follow immediately:

* `coronaMFResidual_eq_of_quotient_isOperatorMF` (Corollary 36.7) — once the
  analytically forced defect quotient is known to be MF, the radical is
  *exactly* the forced defect subgroup, with no hidden extra invisible elements;
* `not_isOperatorMF_of_coronaMFResidual_eq_top` (Proposition 36.8) — defect
  saturation: if the forced defects generate everything, every corona
  representation is trivial and a nontrivial group cannot be MF.

The first of these is the exact-computation principle behind the dossier's
telescope-radical theorem.
-/

namespace GroupApproximation

universe u

variable {H : Type u} [Group H]

/-- **Lemma 36.6.**  A normal subgroup inside the MF radical can be divided out
without losing radical information: the radical is the preimage of the radical
of the quotient. -/
theorem coronaMFResidual_eq_comap (N : Subgroup H) [N.Normal]
    (hN : N ≤ coronaMFResidual H) :
    coronaMFResidual H
      = (coronaMFResidual (H ⧸ N)).comap (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap]
    intro X hX psi
    exact hx X hX (psi.comp (QuotientGroup.mk' N))
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    intro X hX rho
    have hker : ∀ n ∈ N, rho n = 1 := fun n hn => hN hn X hX rho
    have hlift := hx X hX (QuotientGroup.lift N rho hker)
    exact hlift

/-- **Corollary 36.7.**  If the defect quotient is MF, the radical is exactly
the defect subgroup: no further invisible elements are hiding. -/
theorem coronaMFResidual_eq_of_quotient_isOperatorMF [Countable H]
    (N : Subgroup H) [N.Normal] (hN : N ≤ coronaMFResidual H)
    (hMF : IsOperatorMF (H ⧸ N)) : coronaMFResidual H = N := by
  haveI : Countable (H ⧸ N) := Quotient.countable
  rw [coronaMFResidual_eq_comap N hN,
    (isOperatorMF_iff_coronaMFResidual_eq_bot).mp hMF]
  simp

/-- **Proposition 36.8, defect saturation.**  If the forced defects generate the
whole group, every corona representation is trivial, so a nontrivial group
cannot be MF. -/
theorem not_isOperatorMF_of_coronaMFResidual_eq_top [Countable H] [Nontrivial H]
    (h : coronaMFResidual H = ⊤) : ¬ IsOperatorMF H := by
  intro hMF
  rw [isOperatorMF_iff_coronaMFResidual_eq_bot] at hMF
  rw [h] at hMF
  exact top_ne_bot hMF

end GroupApproximation
