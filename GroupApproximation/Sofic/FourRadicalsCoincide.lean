import GroupApproximation.Sofic.ThreeRadicalsCoincide
import GroupApproximation.Sofic.LinearResidual
import GroupApproximation.Algebra.MalcevLinear

/-!
# The all-fields linear residual joins the chain

**Section 46** of the ascending-HNN dossier.  `Sofic/ThreeRadicalsCoincide`
collapses the MF radical, the finite-dimensional unitary residual and the
finite residual onto a single explicit kernel.  The all-fields linear residual
sits in the same place, and the missing inclusion is Mal'cev's theorem: a
finitely generated linear group over any field is residually finite, so a
linear representation cannot see anything invisible to all finite quotients.

* `finiteResidual_le_linearResidual` — the Mal'cev direction, for a finitely
  generated group.  A matrix representation of a group lands in the units, its
  image is a finitely generated linear group, and `MalcevLinear` makes that
  residually finite.
* `four_radicals_eq` — with a residually finite target for the defect quotient
  and the radical containment, all four residuals coincide with its kernel.

The fifth residual of the dossier, the Bohr kernel, has no module in this
development yet -- by Peter--Weyl it coincides with the finite-dimensional
unitary residual, since a compact target separates points by finite-dimensional
unitaries, so the mathematics is immediate and only the module is missing.  The
inclusion it contributes is unconditional, but the reverse needs Peter--Weyl,
which the pinned Mathlib does not have.
-/

namespace GroupApproximation

open MatricialStabilityRadical

universe u

variable {G : Type u} [Group G]

/-- The range of a homomorphism out of a finitely generated group is finitely
generated. -/
theorem range_fg [hfg : Group.FG G] {N : Type*} [Group N] (e : G →* N) :
    (e.range).FG := by
  classical
  obtain ⟨S, hS⟩ : (⊤ : Subgroup G).FG := hfg.out
  refine ⟨S.image e, ?_⟩
  rw [MonoidHom.range_eq_map, ← hS, Finset.coe_image, MonoidHom.map_closure]

/-- **Mal'cev's direction.**  For a finitely generated group, anything killed
by every finite quotient is killed by every finite-dimensional linear
representation over every field: the image of such a representation is a
finitely generated linear group, hence residually finite. -/
theorem finiteResidual_le_linearResidual [Group.FG G] :
    finiteResidual G ≤ linearResidual G := by
  classical
  rw [SetLike.le_def]
  intro x hx
  rw [mem_linearResidual_iff]
  intro F hF d ρ
  letI : Field F := hF
  haveI : Group.ResiduallyFinite ↥((ρ.toHomUnits).range) :=
    MalcevLinear.residuallyFinite_of_fg (F := F) (d := d) _ (range_fg _)
  have hone : (ρ.toHomUnits).rangeRestrict x = 1 := by
    refine Group.residuallyFinite_iff_forall_finiteIndex.mp ‹_› _ fun H hH => ?_
    haveI : (H.comap (ρ.toHomUnits).rangeRestrict).FiniteIndex := by
      refine ⟨?_⟩
      rw [Subgroup.index_comap_of_surjective _ (ρ.toHomUnits).rangeRestrict_surjective]
      exact Subgroup.FiniteIndex.index_ne_zero
    exact mem_finiteResidual_iff.mp hx _ this
  have hval : ρ.toHomUnits x = 1 := by
    have := Subtype.ext_iff.mp hone
    simpa using this
  have hcoe : ((ρ.toHomUnits x : (Matrix (Fin d) (Fin d) F)ˣ) :
      Matrix (Fin d) (Fin d) F) = 1 := by
    rw [hval, Units.val_one]
  rwa [MonoidHom.coe_toHomUnits] at hcoe

/-- **Section 46.3.**  All four residuals coincide with the kernel of a defect
quotient onto a residually finite group. -/
theorem four_radicals_eq [Group.FG G] {P : Type u} [Group P] (Φ : G →* P)
    (hP : IsResiduallyFinite P)
    (hMF : Φ.ker ≤ actualCoronaMFResidual G) :
    actualCoronaMFResidual G = Φ.ker ∧ fdUnitaryResidual G = Φ.ker ∧
      finiteResidual G = Φ.ker ∧ linearResidual G = Φ.ker := by
  obtain ⟨h1, h2, h3⟩ := three_radicals_eq Φ hP hMF
  refine ⟨by rw [h1, h2, h3], by rw [h2, h3], h3, ?_⟩
  refine le_antisymm ?_ ?_
  · exact linearResidual_le_finiteResidual.trans (le_of_eq h3)
  · exact (le_of_eq h3.symm).trans finiteResidual_le_linearResidual

end GroupApproximation
