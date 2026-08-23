import GroupApproximation.Sofic.LiteralTorsionFreeRouterSource
import GroupApproximation.Sofic.LiteralBaseRelations
import GroupApproximation.Sofic.BespokeRouterConstruction

/-!
# Why the literal affine source cannot feed a torsion-free router

The six-generator literal affine base has no nontrivial image in an ordinarily
torsion-free group.  Its three rotation generators have orders dividing
`3, 3, 2`; once they die, the printed action relations first identify the
three translations and then kill them.  Consequently every torsion-free image
of the HNN envelope kills the entire compression defect.  This contradicts
the router's `defect_top` conclusion whenever the protected element survives.

This is a source obstruction, independent of the avatar words, their metric,
or the choice of Kazhdan partner.
-/

namespace GroupApproximation
namespace LiteralTorsionFreeRouterSourceNoGo

open LiteralNonMFPresentation
open LiteralBaseRelations
open LiteralTorsionFreeRouterSource
open SmallCancellationRouter

noncomputable section

/-- Every homomorphism from the literal affine base to an ordinarily
torsion-free group is trivial. -/
theorem base_hom_eq_one_of_isPowerTorsionFree
    {Q : Type*} [Group Q] (hQ : IsPowerTorsionFree Q) (f : Base →* Q) :
    f = 1 := by
  have hx : f x = 1 := by
    apply hQ (f x) 3 (by omega)
    rw [← map_pow, x_cube, map_one]
  have hy : f y = 1 := by
    apply hQ (f y) 3 (by omega)
    rw [← map_pow, y_cube, map_one]
  have hz : f z = 1 := by
    apply hQ (f z) 2 (by omega)
    rw [← map_pow, z_sq, map_one]
  have hv13 : f v1 = f v3 := by
    have h := congrArg f x_conj_v1
    simpa [hx] using h
  have hv21 : f v2 = f v1 := by
    have h := congrArg f x_conj_v2
    simpa [hx] using h
  have hv23 : f v2 = f v3 := hv21.trans hv13
  have hv2 : f v2 = 1 := by
    have h := congrArg f y_conj_v2
    simp only [map_mul, map_inv, hy, one_mul, inv_one] at h
    rw [← hv23] at h
    simpa using h
  have hv1 : f v1 = 1 := hv21.symm.trans hv2
  have hv3 : f v3 = 1 := hv23.symm.trans hv2
  apply MonoidHom.ext
  intro g
  have hg : g ∈ f.ker := by
    apply PresentedGroup.generated_by
      (baseRelators : Set (FreeGroup BaseGenerator)) f.ker
      (fun i ↦ ?_) g
    fin_cases i
    · exact MonoidHom.mem_ker.mpr hv1
    · exact MonoidHom.mem_ker.mpr hv2
    · exact MonoidHom.mem_ker.mpr hv3
    · exact MonoidHom.mem_ker.mpr hx
    · exact MonoidHom.mem_ker.mpr hy
    · exact MonoidHom.mem_ker.mpr hz
  show f g = (1 : Base →* Q) g
  simpa using MonoidHom.mem_ker.mp hg

/-- The compression defect of any bare source over the literal affine base is
killed by every map to an ordinarily torsion-free group. -/
theorem defectNormal_le_ker_of_isPowerTorsionFree
    {E Q : Type*} [Group E] [Group Q]
    (D : BareDefectSourceData Base E) (hQ : IsPowerTorsionFree Q)
    (q : E →* Q) :
    D.core.defectNormal ≤ q.ker := by
  rw [D.core_defectNormal_eq]
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨p, rfl⟩
  change q ⁅D.s, D.iota p⁆ = 1
  rw [map_commutatorElement]
  have hi := DFunLike.congr_fun
    (base_hom_eq_one_of_isPowerTorsionFree hQ (q.comp D.iota)) p
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.one_apply] at hi
  simp [hi]

/-- No torsion-free routing datum can be built from the literal HNN source:
`defect_top` says the killed defect fills the quotient, while protected-ball
injectivity says the quotient is nontrivial. -/
theorem not_routingLemmaData
    {B : Type} [Group B]
    (R : RoutingLemmaData Envelope
      literalBareDefectSourceData.core.defectNormal
      literalBareDefectSourceData.s B) : False := by
  letI : Group R.Quotient := R.groupQuotient
  have hker := defectNormal_le_ker_of_isPowerTorsionFree
    literalBareDefectSourceData R.torsionFree R.route
  have hsmap : R.route literalBareDefectSourceData.s ∈
      literalBareDefectSourceData.core.defectNormal.map R.route := by
    rw [R.defect_top]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hsmap
  have hxone : R.route x = 1 := MonoidHom.mem_ker.mp (hker hx)
  apply R.route_protected_ne_one literalBareDefectSourceData.s_ne_one
  rw [← hxs, hxone]

/-- Existential form used to rule out every attempted literal avatar
certificate, independently of the partner. -/
theorem not_nonempty_routingLemmaData
    {B : Type} [Group B] :
    ¬ Nonempty (RoutingLemmaData Envelope
      literalBareDefectSourceData.core.defectNormal
      literalBareDefectSourceData.s B) := by
  rintro ⟨R⟩
  exact not_routingLemmaData R

end

end LiteralTorsionFreeRouterSourceNoGo
end GroupApproximation
