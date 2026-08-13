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
  constructor
  intro φ
  ext x
  simp only [Subgroup.mem_comap, mem_normMFResidual_iff]
  constructor
  · intro hx
    have h := hx.map φ.symm.toMonoidHom
    simpa using h
  · intro hx
    exact hx.map φ.toMonoidHom

/-- A simple group with one nontrivial norm-MF-invisible element has
residual everything. -/
theorem normMFResidual_eq_top_of_simple [IsSimpleGroup G]
    {x : G} (hx : NormMFInvisible x) (hne : x ≠ 1) :
    normMFResidual G = ⊤ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (normMFResidual_normal (G := G)) with
    hbot | htop
  · exfalso
    have hx' : x ∈ normMFResidual G := mem_normMFResidual_iff.mpr hx
    rw [hbot] at hx'
    exact hne (Subgroup.mem_bot.mp hx')
  · exact htop

/-- Full residual makes every homomorphism to a countable weak-MF group
trivial. -/
theorem map_eq_one_of_normMFResidual_eq_top
    (htop : normMFResidual G = ⊤) {H : Type*} [Group H] [Countable H]
    (hH : IsWeakMF H) (f : G →* H) (g : G) : f g = 1 := by
  have hg : g ∈ normMFResidual G := by rw [htop]; exact Subgroup.mem_top g
  have hfg : f g ∈ normMFResidual H :=
    mem_normMFResidual_iff.mpr ((mem_normMFResidual_iff.mp hg).map f)
  rw [normMFResidual_eq_bot_of_isWeakMF hH] at hfg
  exact Subgroup.mem_bot.mp hfg

end GroupApproximation
