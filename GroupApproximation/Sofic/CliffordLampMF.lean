import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.CentralInvolutionFinite

/-!
# The presented Clifford lamp group is locally finite, hence operator-MF

`CliffordLamp X` is the presented group on a central sign together with one
involution per site, any two distinct site involutions commuting up to that
sign.  This is exactly the hypothesis pattern of
`isLocallyFiniteGroup_of_central_involution`, so the lamp group is locally
finite for every site set, and operator-MF whenever the site set is
countable.

This is the lamp half of the non-MF witness group of
`LiteralNonMFLinearWitness`: the Clifford lamp normal subgroup there is
approximable for elementary reasons, and any failure of MF in the ambient
semidirect product therefore comes from the telescope direction rather than
from the lamps.
-/

namespace GroupApproximation
namespace CliffordLamp

open scoped commutatorElement

universe u

variable (X : Type u)

/-- The sign together with the site involutions generate the whole lamp
group. -/
theorem closure_sign_lamp_eq_top :
    Subgroup.closure (insert (sign X) (Set.range (lamp X))) = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  refine mem_subgroup_of_sign_mem_of_lamp_mem X _ ?_ ?_ g
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact fun x ↦ Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨x, rfl⟩)

/-- Two site involutions commute up to the sign, at equal sites trivially. -/
theorem lamp_commutator_mem_zpowers (x y : X) :
    lamp X x * lamp X y * (lamp X x)⁻¹ * (lamp X y)⁻¹ ∈
      Subgroup.zpowers (sign X) := by
  by_cases hxy : x = y
  · subst hxy
    have h : lamp X x * lamp X x * (lamp X x)⁻¹ * (lamp X x)⁻¹ = 1 := by group
    rw [h]
    exact Subgroup.one_mem _
  · have h := commutator_lamp_lamp X hxy
    rw [commutatorElement_def] at h
    rw [h]
    exact Subgroup.mem_zpowers _

/-- **The presented Clifford lamp group is locally finite.** -/
theorem isLocallyFiniteGroup_cliffordLamp :
    IsLocallyFiniteGroup (CliffordLamp X) :=
  isLocallyFiniteGroup_of_central_involution (sign_sq X)
    (fun g ↦ sign_commute X g) (closure_sign_lamp_eq_top X)
    (by rintro _ ⟨x, rfl⟩; exact lamp_sq X x)
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact lamp_commutator_mem_zpowers X x y)

/-- The lamp group has exact finite local models. -/
theorem isLEF_cliffordLamp : IsLEF (CliffordLamp X) :=
  isLEF_of_locallyFinite (isLocallyFiniteGroup_cliffordLamp X)

/-- **A countable Clifford lamp group is operator-MF.** -/
theorem isOperatorMF_cliffordLamp [Countable X] :
    IsOperatorMF (CliffordLamp X) :=
  isOperatorMF_of_locallyFinite (isLocallyFiniteGroup_cliffordLamp X)

/-- Any subgroup of a lamp group -- in particular the lamp part of a marked
compression witness -- is locally finite. -/
theorem isLocallyFiniteGroup_subgroup (H : Subgroup (CliffordLamp X)) :
    IsLocallyFiniteGroup H :=
  (isLocallyFiniteGroup_cliffordLamp X).comap H.subtype
    (fun _ _ h ↦ Subtype.ext h)

/-! ## Positive controls -/

example : IsLocallyFiniteGroup (CliffordLamp ℕ) :=
  isLocallyFiniteGroup_cliffordLamp _

example : IsOperatorMF (CliffordLamp ℕ) := isOperatorMF_cliffordLamp _

/-- The sign really is nontrivial, so these are not claims about the trivial
group. -/
example : sign ℕ ≠ 1 := sign_ne_one _

end CliffordLamp
end GroupApproximation
