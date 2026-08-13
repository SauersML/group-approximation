import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# Characteristic and simple-envelope consequences of the MF residual

`NormMFInvisible.map` makes the operator-norm MF residual functorial; the
detector file records normality.  This file adds the two envelope-level
consequences: the residual is characteristic, and in a simple group one
nontrivial invisible element poisons everything — the residual is the whole
group, so every homomorphism into a countable weak-MF group is trivial.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- The operator-norm MF residual is characteristic. -/
instance normMFResidual_characteristic :
    (normMFResidual G).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.mpr fun φ x hx => ?_
  have h := (mem_normMFResidual_iff.mp hx).map φ.toMonoidHom
  simpa using h

/-- A simple group with one nontrivial norm-MF-invisible element has
residual everything. -/
theorem normMFResidual_eq_top_of_simple [IsSimpleGroup G]
    {x : G} (hx : NormMFInvisible x) (hne : x ≠ 1) :
    normMFResidual G = ⊤ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top normMFResidual_normal with hbot | htop
  · exact absurd (hbot ▸ mem_normMFResidual_iff.mpr hx)
      (by simpa [Subgroup.mem_bot] using hne)
  · exact htop

/-- Full residual makes every homomorphism to a countable weak-MF group
trivial. -/
theorem map_eq_one_of_normMFResidual_eq_top
    (htop : normMFResidual G = ⊤) {H : Type*} [Group H] [Countable H]
    (hH : IsWeakMF H) (f : G →* H) (g : G) : f g = 1 := by
  have hg : g ∈ normMFResidual G := htop ▸ Subgroup.mem_top g
  have hfg : f g ∈ normMFResidual H :=
    mem_normMFResidual_iff.mpr ((mem_normMFResidual_iff.mp hg).map f)
  have hbot := normMFResidual_eq_bot_of_isWeakMF hH
  simpa [Subgroup.mem_bot] using hbot ▸ hfg

end GroupApproximation
