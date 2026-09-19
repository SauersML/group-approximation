import GroupApproximation.Monsters.P13CircumcenterRoute
import GroupApproximation.Sofic.LiteralTranslationOrbit
import GroupApproximation.Sofic.LiteralBaseRotationRetract

/-!
# Step 3 of `prop:literal-base-T`, through the printed objects

Manuscript target: Step 3 of the printed proof of Proposition
`\ref{prop:literal-base-T}`.

**That proof no longer exists.**  Commit `3a45fa60` ("Editorial pass: rewrite
orbit collapse, cut what nothing uses") replaced the three-step property-`(T)`
argument with a one-paragraph citation of `\ref{rem:classical-base}` and
`\cite[Example~1.7.4(i)]{BHV}`; the proposition's statement is unchanged and
still badged, but every clause quoted below has been deleted from the
manuscript, and `notes/P13_STEP_AUDIT.md` is graded against the deleted text.
The quotations are kept verbatim so the audit rows stay readable, and the
declarations are kept because they are correct and imported; none of them is
badgeable any more.

This module gives Lean counterparts to the Step-3 clauses that the
step-for-step audit (`notes/P13_STEP_AUDIT.md`, §3) recorded as `MISMATCH` or
`MISSING`, using the objects the manuscript named rather than the
equally-valid substitutes the existing development uses.

* **T3.11** *"The orbit of `p` under the translation subgroup is bounded, so
  the Hilbert-space circumcenter argument gives a translation-fixed vector `q`
  with `‖q-p‖ ≤ 1/8`"* (item 3 of Step 3).  Routed through the genuine
  circumcenter — the centre of the smallest enclosing ball — of
  `Kazhdan/HilbertCircumcenter.lean`, via
  `P13CircumcenterRoute.exists_near_fixedSubspace_circumcenter`, instead of the
  minimal-norm point of the closed convex hull of the orbit.
* **T3.04** *"The third basis translation needs no separate control:
  `v₁ = x v₂ x⁻¹` by the displayed `x`-action, and conjugation by the fixed
  unitary of `x` preserves displacements of vectors fixed by the linear
  subgroup"* (item 1 of Step 3).  Both halves are proved here.  (The existing
  development omits `v₁` for a different, also correct, reason: the
  two-conjugate normal form of item 2 already covers it.)
* **T3.02** *"every lattice element is a product of two linear-subgroup
  conjugates of basis translations … Hence every translation displaces `p` by
  at most `1/8`"* (item 2 of Step 3).  Stated with a displacement hypothesis on
  all three *basis* translations, which is what the printed item 2 assumes, so
  that T3.04 is a genuine input to it rather than an unused aside.
* **T3.01** *"the generators `x,y,z` of `B` satisfy the relators of `R`, so
  `R` maps to the linear subgroup of `B` they generate"* (the opening of
  Step 3).
  Property `(T)` is transported along that **surjection** onto the linear
  subgroup, by the quotient permanence the manuscript already invokes in
  Step 2 — not along the isomorphism `Rotation ≃* rotations`, which is a
  stronger fact than the printed one.
* **T3.03** the unstated `κ ≤ 1` normalization on which the printed constant
  `3/64` depends.  Here it is *derived* from Step 2's Kazhdan pair rather than
  assumed, so nothing beyond the printed `κ > 0` is required as input.

`Sofic/LiteralBasePropertyTBridge.lean` — the module on the badged path from
`prop:literal-base-T` — invokes T3.01, T3.02, T3.03 and T3.11 from here, so the
badged declaration travels the printed route.  Nothing in the convex-hull
development of `Kazhdan/HilbertConvexFixedPoint.lean` is modified; it remains
available as the alternate fixed-point engine.
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
is the second half of the manuscript's justification for omitting the third
basis translation from the control set. -/
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
  linarith

/-! ## T3.11 — the circumcenter of the bounded translation orbit -/

/-- **T3.11, first clause.**  *"The orbit of `p` under the translation subgroup
is bounded."* -/
theorem t3_11_translationOrbit_isBounded
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hbound : ∀ t : translations, ‖rho t.1 p - p‖ ≤ 1 / 8) :
    Bornology.IsBounded (Set.range fun t : translations ↦ rho t.1 p) :=
  P13CircumcenterRoute.isBounded_orbit rho translations p hbound

/-- **T3.11.**  *"…so the Hilbert-space circumcenter argument gives a
translation-fixed vector `q` with `‖q-p‖ ≤ 1/8`."*  The witness is the
circumcenter of the translation orbit of `p`: the centre of the smallest
enclosing ball, characterized as the unique minimizer of the covering radius.

The extra conjunct records that the witness genuinely realizes the Chebyshev
radius of the orbit, so the printed object is the one produced. -/
theorem t3_11_exists_translation_fixed_circumcenter [CompleteSpace E]
    (rho : Base →* (E ≃ₗᵢ[ℝ] E)) (p : E)
    (hbound : ∀ t : translations, ‖rho t.1 p - p‖ ≤ 1 / 8) :
    ∃ q : E,
      Circumcenter.coveringRadius
          (Set.range fun t : translations ↦ rho t.1 p) q =
        Circumcenter.chebyshevRadius
          (Set.range fun t : translations ↦ rho t.1 p) ∧
      (∀ t : translations, rho t.1 q = q) ∧ ‖q - p‖ ≤ 1 / 8 :=
  P13CircumcenterRoute.exists_circumcenter_fixed_norm_sub_le rho translations p
    hbound

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

@[simp] theorem rotationToRotations_coe (r : Rotation) :
    (rotationToRotations r : Base) = rotationToBase r := rfl

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

/-- **T3.03.**  The printed Step 3 offers only *"a `κ>0` forming a Kazhdan
pair"*, while the displayed constant `3/64` of item 2 needs `κ ≤ 1`.  The gap
is not a hypothesis: shrinking the tolerance of a Kazhdan pair leaves it a
Kazhdan pair, so `min κ 1` is available for free. -/
theorem t3_03_kazhdanPair_min_one {S : Finset rotations} {kappa : ℝ}
    (hS : IsKazhdanPair.{0, w} rotations S kappa) :
    IsKazhdanPair.{0, w} rotations S (min kappa 1) ∧ min kappa 1 ≤ 1 :=
  ⟨IsKazhdanPair.shrink hS (lt_min hS.1 zero_lt_one) (min_le_left _ _),
    min_le_right _ _⟩

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
