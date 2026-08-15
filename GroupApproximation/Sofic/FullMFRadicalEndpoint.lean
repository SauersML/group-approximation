import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# The frozen public endpoint of the defect-routing program

This module states the Main Theorem of the routing program in its final
public form, with no construction structures, endpoint wrappers, or
formalization vocabulary in the statement: IF the two-stage relative
common-quotient construction produces routing data for some
Fournier--Facio defect datum, THEN there exists a two-generated,
finitely presented, torsion-free group with property (T) whose literal
CDE MF radical is the whole group — and every nontrivial quotient of
that group fails to be MF.

The hypotheses are a single `Nonempty (DefectRoutingData D)`.  The
decisive open obligation of the program is to discharge that hypothesis
by an unconditional construction; every formalization step should be
judged by whether it moves that discharge closer.  The statements below
are the specification frozen in advance: whatever the construction
produces must land exactly here, and nothing downstream may widen the
interface.
-/

namespace GroupApproximation
namespace FullMFRadicalEndpoint

universe u

/-- **The Main Theorem, frozen.**  Routing data yields a two-generated,
finitely presented, torsion-free property-(T) group whose literal CDE
MF radical is everything. -/
theorem exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical
    {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (h : Nonempty (DefectRoutingData.{u} D)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ := by
  obtain ⟨R⟩ := h
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  exact ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    R.cdeMFResidual_eq_top⟩

/-- **Hereditary form, frozen.**  Routing data yields a nontrivial group,
with the same profile, all of whose nontrivial quotients fail to be MF —
in particular the group itself is not MF, and it admits no nontrivial
finite, residually finite, or MF quotient of any kind. -/
theorem exists_group_with_every_nontrivial_quotient_not_isCDEOperatorMF
    {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (h : Nonempty (DefectRoutingData.{u} D)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      ∀ (H : Type) (_ : Group H) (_ : Nontrivial H) (f : Q →* H),
        Function.Surjective f → ¬ IsCDEOperatorMF H := by
  obtain ⟨R⟩ := h
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  refine ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    ?_⟩
  intro H _ _ f hf
  letI : Countable H := hf.countable
  exact R.quotient_not_isCDEOperatorMF f hf

end FullMFRadicalEndpoint
end GroupApproximation
