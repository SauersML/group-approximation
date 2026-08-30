import GroupApproximation.Monsters.P13CircumcenterRoute
import GroupApproximation.Sofic.LiteralTranslationOrbit
import GroupApproximation.Sofic.LiteralBaseRotationRetract

/-!
# Circumcenter route for the P13 property-(T) argument

This module supplies the geometric ingredients used by
`LiteralBasePropertyTBridge`:

* bounded translation orbits admit nearby fixed circumcenters;
* conjugation by a unitary fixing the base point preserves displacement;
* lattice elements are controlled by conjugates of basis translations;
* property `(T)` passes to the generated rotation quotient; and
* the required normalization `κ ≤ 1` follows from the Kazhdan pair.

The fixed point is the centre of the smallest enclosing ball, as developed in
`Kazhdan/HilbertCircumcenter.lean`. The convex-hull construction remains an
independent alternative.
-/

namespace GroupApproximation
namespace P13CircumcenterRouteStep3

open LiteralBaseRelations LiteralBaseTranslationNormal
open LiteralBaseRotationRetract LiteralTranslationOrbit

noncomputable section

universe uE w

private abbrev Base := LiteralNonMFPresentation.Base

/-! ## A general displacement identity for conjugation by a fixing element -/

section General

variable {G : Type*} [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Conjugation by a fixed unitary preserves displacements.**  If `ρ(r)`
fixes `p`, then `r v r⁻¹` displaces `p` by exactly as much as `v` does.  This
is the identity used to omit the third basis translation from the control
set. -/
theorem norm_conj_displacement_eq_of_fixed
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (p : E) {r : G} (hr : rho r p = p) (v : G) :
    ‖rho (r * v * r⁻¹) p - p‖ = ‖rho v p - p‖ := by
  have hri : (rho r)⁻¹ p = p := by
    have h := congrArg (fun q : E ↦ (rho r)⁻¹ q) hr
    simpa using h.symm
  calc
    ‖rho (r * v * r⁻¹) p - p‖ = ‖rho r (rho v p - p)‖ := by
      congr 1
      simp only [map_mul, map_inv, LinearIsometryEquiv.coe_mul,
        Function.comp_apply, map_sub, hri, hr]
    _ = ‖rho v p - p‖ := (rho r).norm_map _

end General

/-! ## T3.04 — the third basis translation needs no separate control -/

/-- **T3.04, first half.**  `v₁ = x v₂ x⁻¹`, by the displayed `x`-action
relator of the twenty-relator presentation. -/
theorem t3_04_v1_eq_x_conj_v2 :
    LiteralBaseRelations.v1 =
      LiteralBaseRelations.x * LiteralBaseRelations.v2 *
        LiteralBaseRelations.x⁻¹ :=
  x_conj_v2.symm

section Displacement

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **T3.04.**  A vector fixed by the linear subgroup is displaced by `v₁`
exactly as much as by `v₂`, because `v₁ = x v₂ x⁻¹` and `x` lies in the linear
subgroup.  This is the manuscript's reason for leaving `v₁` out of the finite
control set. -/
theorem t3_04_norm_v1_displacement_eq
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p) :
    ‖rho LiteralBaseRelations.v1 p - p‖ =
      ‖rho LiteralBaseRelations.v2 p - p‖ := by
  have hx : rho LiteralBaseRelations.x p = p :=
    hfixed ⟨LiteralBaseRelations.x, x_mem_rotations⟩
  rw [t3_04_v1_eq_x_conj_v2]
  exact norm_conj_displacement_eq_of_fixed rho p hx LiteralBaseRelations.v2

/-- **T3.04, in the form the printed argument uses it.**  Any displacement
bound obtained for `v₂` at a linear-subgroup-fixed vector transfers verbatim to
`v₁`, so no separate control on `v₁` is needed. -/
theorem t3_04_norm_v1_displacement_lt
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p) {c : ℝ}
    (hv2 : ‖rho LiteralBaseRelations.v2 p - p‖ < c) :
    ‖rho LiteralBaseRelations.v1 p - p‖ < c := by
  rw [t3_04_norm_v1_displacement_eq rho p hfixed]
  exact hv2

/-- **T3.04, packaged for item 2.**  The printed item 2 needs a displacement
bound at `p` for *each* of the three basis translations, and the printed control
set supplies only `v₂` and `v₃`.  This lemma closes that gap the way the
manuscript does: `v₁`'s bound is not an extra hypothesis, it is derived from
`v₁ = x v₂ x⁻¹` and the invariance of displacements under conjugation by the
linear subgroup.

This is the form in which `Sofic/LiteralBasePropertyTBridge.lean` consumes
T3.04, so the printed justification for omitting `v₁` from the control set is
now load-bearing rather than decorative. -/
theorem t3_04_basis_displacement_lt
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p) {c : ℝ}
    (hv2 : ‖rho LiteralBaseRelations.v2 p - p‖ < c)
    (hv3 : ‖rho LiteralBaseRelations.v3 p - p‖ < c) :
    ∀ v ∈ ({LiteralBaseRelations.v1, LiteralBaseRelations.v2,
        LiteralBaseRelations.v3} : Set Base), ‖rho v p - p‖ < c := by
  rintro v (rfl | rfl | rfl)
  · exact t3_04_norm_v1_displacement_lt rho p hfixed hv2
  · exact hv2
  · exact hv3

/-! ## T3.02 — from the basis translations to the whole lattice -/

/-- **Step 3, item 2, endpoint.**  *"Consequently every lattice element is a
product of two linear-subgroup conjugates of basis translations … Hence every
translation displaces `p` by at most `1/8`."*

The hypothesis is the printed one: a common displacement bound `c` at `p` for
each of the three *basis* translations `v₁, v₂, v₃`.  The two-conjugate normal
form of `LiteralTranslationOrbit` then doubles it, giving `2c` for every element
of the translation subgroup; with the printed `c = 3/64` this is the printed
`3/32 ≤ 1/8`.

Quantifying over all three basis translations, rather than over the two that the
repo's normal form happens to use, is what makes T3.04 an input to this step, as
printed. -/
theorem t3_02_norm_translation_displacement_le
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hfixed : ∀ r : rotations, rho (r : Base) p = p) {c : ℝ}
    (hbasis : ∀ v ∈ ({LiteralBaseRelations.v1, LiteralBaseRelations.v2,
        LiteralBaseRelations.v3} : Set Base), ‖rho v p - p‖ < c)
    (t : translations) :
    ‖rho t.1 p - p‖ ≤ 2 * c := by
  have h := norm_translation_displacement_le_of_rotations_fixed rho p hfixed t.2
  have h2 := hbasis LiteralBaseRelations.v2 (by simp)
  have h3 := hbasis LiteralBaseRelations.v3 (by simp)
  linarith only [h, h2, h3]

/-! ## T3.11 — the circumcenter of the bounded translation orbit -/

/-- **T3.11, in the shape the bridge consumes.**  Signature-identical to
`HilbertConvexFixedPoint.exists_near_fixedSubspace rho translations p`, and it
is what `Sofic/LiteralBasePropertyTBridge.lean` now calls, so the badged
property-`(T)` endpoint obtains its translation-fixed vector from the printed
circumcenter. -/
theorem t3_11_exists_near_translationFixedSubspace [CompleteSpace E]
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hbound : ∀ t : translations, ‖rho t.1 p - p‖ ≤ 1 / 8) :
    ∃ q ∈ KazhdanFixedSpace.fixedSubspace rho translations, ‖q - p‖ ≤ 1 / 8 :=
  P13CircumcenterRoute.exists_near_fixedSubspace_circumcenter rho translations p
    hbound

end Displacement

/-! ## T3.01 — the linear subgroup receives `R` by a surjection -/

/-- The canonical map of the abstract rotation presentation **onto** the linear
subgroup of the literal base generated by `x,y,z`.  Only surjectivity is used
below; no retraction and no injectivity claim enters. -/
def rotationToRotations : Rotation →* rotations :=
  rotationToBase.codRestrict rotations fun r => by
    rw [← rotationToBase_range]
    exact ⟨r, rfl⟩

/-- **T3.01.**  *"`R` maps to the linear subgroup of `B` they generate"* — and
the map is onto, since the range of `rotationToBase` is exactly `rotations`. -/
theorem rotationToRotations_surjective :
    Function.Surjective rotationToRotations := by
  intro r
  have hr : (r : Base) ∈ rotationToBase.range := by
    rw [rotationToBase_range]
    exact r.property
  rcases hr with ⟨q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

/-- **T3.01, the property-`(T)` transfer as printed.**  Property `(T)` passes
to quotients — the very permanence property Step 2 invokes for
`P₁₃ ↠ R` — so it passes along the surjection `R ↠ ⟨x,y,z⟩`.  No isomorphism
`Rotation ≃* rotations`, and hence no retraction `Base →* Rotation`, is used. -/
theorem t3_01_rotations_hasKazhdanPropertyT
    (hRotation : HasKazhdanPropertyT.{0, 0} Rotation) :
    HasKazhdanPropertyT.{0, 0} rotations :=
  HasKazhdanPropertyT.of_surjective rotationToRotations
    rotationToRotations_surjective hRotation

/-! ## T3.03 — the `κ ≤ 1` normalization, derived rather than assumed -/

/-- **T3.03, at the point Step 2 hands over to Step 3.**  Step 2's conclusion
already delivers a normalized Kazhdan pair for the linear subgroup: a finite
control set and a tolerance in `(0,1]`.  Nothing beyond the printed `κ>0` is
assumed anywhere. -/
theorem t3_03_exists_normalized_pair
    (hRotations : HasKazhdanPropertyT.{0, w} rotations) :
    ∃ S : Finset rotations, ∃ kappa : ℝ,
      0 < kappa ∧ kappa ≤ 1 ∧ IsKazhdanPair.{0, w} rotations S kappa := by
  obtain ⟨S, kappa, -, hpos, hone, hS⟩ := hRotations.exists_identity_pair
  exact ⟨S, kappa, hpos, hone, hS⟩

end

end P13CircumcenterRouteStep3
end GroupApproximation
