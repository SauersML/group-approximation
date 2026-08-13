import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Sofic.WeakMFTransfer

/-!
# Characteristic and simple-envelope consequences of the MF residual

`NormMFInvisible.map` makes the operator-norm MF residual functorial; the
detector file records normality.  This file adds the two envelope-level
consequences: the residual is characteristic, and in a simple group one
nontrivial invisible element poisons everything — the residual is the whole
group.  For a countable source, every homomorphism into an arbitrary weak-MF
group is then trivial: its range is countable and inherits weak-MF from the
target.
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

/-- For a countable source, full residual makes every homomorphism to an
arbitrary weak-MF group trivial.  No countability assumption on the target is
needed: the homomorphism factors through its countable range, and weak-MF
passes to subgroups. -/
theorem map_eq_one_of_normMFResidual_eq_top
    [Countable G] (htop : normMFResidual G = ⊤) {H : Type*} [Group H]
    (hH : IsWeakMF H) (f : G →* H) (g : G) : f g = 1 := by
  letI : Countable f.range :=
    Function.Surjective.countable f.rangeRestrict_surjective
  have hRangeMF : IsWeakMF f.range :=
    isWeakMF_of_injective f.range.subtype Subtype.val_injective hH
  have hg : g ∈ normMFResidual G := by rw [htop]; exact Subgroup.mem_top g
  have hfg : f.rangeRestrict g ∈ normMFResidual f.range :=
    mem_normMFResidual_iff.mpr
      ((mem_normMFResidual_iff.mp hg).map f.rangeRestrict)
  rw [normMFResidual_eq_bot_of_isWeakMF hRangeMF] at hfg
  simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hfg)

end GroupApproximation
