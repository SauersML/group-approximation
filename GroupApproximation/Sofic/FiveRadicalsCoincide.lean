import GroupApproximation.Sofic.FourRadicalsCoincide
import GroupApproximation.Analysis.PeterWeylProfinite

/-!
# The five-way coincidence

**Section 46.5** of the ascending-HNN dossier, the last clause.
`Sofic/FourRadicalsCoincide` collapses the MF radical, the finite-dimensional
unitary residual, the finite residual and the all-fields linear residual onto
one kernel.  The fifth is the Bohr residual of `Analysis/PeterWeylProfinite`,
and it joins the chain from two inclusions in opposite directions:

* `bohrResidual ≤ finiteResidual` is unconditional -- a finite group with the
  discrete topology is a compact target;
* `finiteResidual ≤ bohrResidual` for a finitely generated group is Mal'cev's
  direction followed by Peter--Weyl: the finite residual is killed by every
  representation over every field (`finiteResidual_le_linearResidual`), and a
  compact target whose points finite-dimensional representations separate can
  therefore not see it.

The second uses the analytic core of Peter--Weyl, which the pinned Mathlib does
not have; it enters as the single named hypothesis `PeterWeyl.SeparatesPoints`,
exactly as `Analysis/PeterWeylProfinite` isolates it.  So `five_radicals_eq`
carries one classical input and nothing else.

For **profinite** targets no input is needed at all: van Dantzig gives the
separation outright, so `five_radicals_eq_profinite` states the same conclusion
unconditionally, with the Bohr clause read as "every homomorphism into a
profinite group kills the kernel".  That is the form the dossier's finite-index
and profinite-twin sections actually consume.
-/

namespace GroupApproximation

open MatricialStabilityRadical PeterWeyl

universe u

variable {G : Type u} [Group G]

/-- **`Rad_Bohr = Res_fin` for a finitely generated group**, given the
separation core of Peter--Weyl. -/
theorem bohrResidual_eq_finiteResidual [Group.FG G]
    (hPW : SeparatesPoints.{u}) :
    bohrResidual G = finiteResidual G := by
  refine le_antisymm bohrResidual_le_finiteResidual fun x hx => ?_
  exact linearResidual_le_bohrResidual_of_separates hPW
    (mem_linearResidual_iff.mp (finiteResidual_le_linearResidual hx))

/-- **Section 46.5.**  With a residually finite target for the defect quotient
and the radical containment, all five residuals of the dossier coincide with
its kernel: the MF radical, the finite-dimensional unitary residual, the finite
residual, the all-fields linear residual and the Bohr kernel. -/
theorem five_radicals_eq [Group.FG G] (hPW : SeparatesPoints.{u})
    {P : Type u} [Group P] (Φ : G →* P) (hP : IsResiduallyFinite P)
    (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = Φ.ker ∧ fdUnitaryResidual G = Φ.ker ∧
      finiteResidual G = Φ.ker ∧ linearResidual G = Φ.ker ∧
      bohrResidual G = Φ.ker := by
  obtain ⟨h1, h2, h3, h4⟩ := four_radicals_eq Φ hP hMF
  exact ⟨h1, h2, h3, h4, (bohrResidual_eq_finiteResidual hPW).trans h3⟩

/-- **The unconditional form.**  For profinite targets the separation input is
a theorem, so the five-way coincidence needs no hypothesis beyond those of the
four-way one: the four residuals are the kernel, and every homomorphism from
`G` into a profinite group kills it. -/
theorem five_radicals_eq_profinite {P : Type u} [Group P] (Φ : G →* P)
    (hP : IsResiduallyFinite P) (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = Φ.ker ∧ fdUnitaryResidual G = Φ.ker ∧
      finiteResidual G = Φ.ker ∧
      (∀ {C : Type u} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
        [CompactSpace C] [TotallyDisconnectedSpace C] (f : G →* C),
          Φ.ker ≤ f.ker) := by
  obtain ⟨h1, h2, h3⟩ := three_radicals_eq Φ hP hMF
  refine ⟨by rw [h1, h2, h3], by rw [h2, h3], h3, ?_⟩
  intro C _ _ _ _ _ f
  exact le_trans (le_of_eq h3.symm) (finiteResidual_le_ker_of_profinite f)

/-- **The strongest unconditional form, for an arbitrary visible quotient.**
Four radicals equal the kernel outright; the Bohr residual is trapped inside it,
because finite groups are compact targets; and every homomorphism into a
profinite group kills it, van Dantzig supplying the separation.  No hypothesis
beyond those of the four-way theorem, and in particular no Peter--Weyl.

This is `five_radicals_eq` with the one classical input removed and the Bohr
clause weakened to exactly what survives without it: an upper bound in general,
an equality on totally disconnected targets. -/
theorem four_radicals_eq_and_bohr_bounds [Group.FG G] {P : Type u} [Group P]
    (Φ : G →* P) (hP : IsResiduallyFinite P)
    (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = Φ.ker ∧ fdUnitaryResidual G = Φ.ker ∧
      finiteResidual G = Φ.ker ∧ linearResidual G = Φ.ker ∧
      bohrResidual G ≤ Φ.ker ∧
      (∀ {C : Type u} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
        [CompactSpace C] [TotallyDisconnectedSpace C] (f : G →* C),
          Φ.ker ≤ f.ker) := by
  obtain ⟨h1, h2, h3, h4⟩ := four_radicals_eq Φ hP hMF
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [← h3]; exact bohrResidual_le_finiteResidual
  · intro C _ _ _ _ _ f
    exact le_trans (le_of_eq h3.symm) (finiteResidual_le_ker_of_profinite f)

end GroupApproximation
