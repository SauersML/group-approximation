import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Torsion
import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Separation
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.Approximation
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# The abelian boundary

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160):

> For every countable abelian group `A`, the group `A^{(X)} ⋊ G_*` is MF if and only if `A` is
> torsion-free.

The torsion direction is `isAddTorsionFree_of_isOperatorMF` (`Torsion.lean`).  For the
torsion-free direction (tex lines 2098--2150) we show that every nonidentity element survives
some corona representation, and then use the corona-residual characterization of MF for
countable groups:

* an element with nontrivial `G_*`-coordinate is detected by the faithful corona representation
  of `G_*` (`gstar_isOperatorMF`) composed with the projection;
* a nontrivial configuration is detected by `exists_corona_separating`.  This uses residual
  finiteness of `G_*` (`gstar_residuallyFinite`) and an enumeration of `Γ_*`.

Main declarations: `torsionFree_isOperatorMF`, `notesAbelianBoundary`.
-/

namespace GroupApproximation.Full.NN06

open SemidirectProduct GroupApproximation.Full.NN05

noncomputable section

variable {A : Type} [AddCommGroup A]

/-- An enumeration of the countable subgroup `Γ_* ≤ G_*` (tex line 2120, `e_0, e_1, …`). -/
theorem exists_enum_gamma :
    ∃ e : ℕ → Gstar, (∀ j, e j ∈ ofGamma.range) ∧ ∀ h ∈ ofGamma.range, ∃ j, e j = h := by
  obtain ⟨f, hf⟩ := exists_surjective_nat ↥(ofGamma.range : Subgroup Gstar)
  refine ⟨fun j => (f j : Gstar), fun j => (f j).2, fun h hh => ?_⟩
  obtain ⟨j, hj⟩ := hf ⟨h, hh⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- **Every nonidentity element of `A^{(X)} ⋊ G_*` is visible in some corona**
(tex lines 2134--2150), for torsion-free `A`. -/
theorem exists_corona_ne_one [IsAddTorsionFree A] {w : AbelianLamp A} (hw : w ≠ 1) :
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : AbelianLamp A →* NormMatrixCoronaUnitary X, rho w ≠ 1 := by
  by_cases hr : w.right = 1
  · have hl : w.left ≠ 1 := fun hl =>
      hw (SemidirectProduct.ext (hl.trans one_left.symm) (hr.trans one_right.symm))
    have hwl : w = inl w.left :=
      SemidirectProduct.ext (left_inl w.left).symm (hr.trans (right_inl w.left).symm)
    obtain ⟨e, he, hsurj⟩ := exists_enum_gamma
    obtain ⟨X, hX, rho, hrho⟩ := exists_corona_separating gstar_residuallyFinite e he hsurj hl
    exact ⟨X, hX, rho, fun h => hrho ((congrArg rho hwl).symm.trans h)⟩
  · obtain ⟨X, hX, rho, hinj⟩ := gstar_isOperatorMF
    refine ⟨X, hX, rho.comp (SemidirectProduct.rightHom : AbelianLamp A →* Gstar),
      fun h => hr ?_⟩
    have h' : rho w.right = rho 1 := h.trans (map_one rho).symm
    exact hinj h'

/-- **`thm:notes-abelian-boundary`, torsion-free direction.**  If `A` is countable and
torsion-free, then `A^{(X)} ⋊ G_*` is MF. -/
theorem torsionFree_isOperatorMF [Countable A] [IsAddTorsionFree A] :
    IsOperatorMF (AbelianLamp A) := by
  rw [isOperatorMF_iff_coronaMFResidual_eq_bot]
  refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
  by_contra hw1
  obtain ⟨X, hX, rho, hrho⟩ := exists_corona_ne_one hw1
  exact hrho ((mem_coronaMFResidual_iff.mp hw) X hX rho)

/-- **`thm:notes-abelian-boundary`** (tex lines 2078--2160): for every countable abelian
group `A`, the group `A^{(X)} ⋊ G_*` is MF if and only if `A` is torsion-free. -/
theorem notesAbelianBoundary [Countable A] :
    IsOperatorMF (AbelianLamp A) ↔ IsAddTorsionFree A :=
  ⟨isAddTorsionFree_of_isOperatorMF, fun hA => @torsionFree_isOperatorMF A _ _ hA⟩

end

#audit_axioms exists_enum_gamma
#audit_axioms exists_corona_ne_one
#audit_axioms torsionFree_isOperatorMF
#audit_axioms notesAbelianBoundary

end GroupApproximation.Full.NN06
