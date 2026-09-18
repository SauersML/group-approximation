import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetNatural
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetActionAssembly

/-!
# The Cuntz-picture action preserves vanishing boundary maps

Lane `TWWSch3d3-3B`, work order `WO-TWWSchafhauser-3d3-3B`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), via C. Schafhauser, J. reine angew. Math. 759
(2020), §§4--5.

Let `D` be Cuntz-picture data `A ←p— M A —c→ F A` (`ExtSSCuntzData`). The action of
`x = [f] ∈ [F A, F B]` on `Ext(-, J)` is `x^* = e_A⁻¹ ∘ f^* ∘ e_B`. Its defining property is
`p^* ε_A⁻¹ (x^* ξ) = c^* f^* e_B ξ`, and `c^* e_B ξ = p^* ε_B⁻¹ ξ`. The index and exponential
maps are natural in the first variable (`ExtGroup.boundaryZero_comap`,
`ExtGroup.boundaryOne_comap`; J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §1). Hence

  `∂ ξ = 0 ⇒ ∂(e_B ξ) ∘ c_* = 0 ⇒ ∂(e_B ξ) = 0 ⇒ ∂(x^* ξ) ∘ p_* = 0 ⇒ ∂(x^* ξ) = 0`,

provided `c_*` and `p_*` are surjective on `K_*`. In the model, `c` is the corner embedding
`qA → 𝒦 ⊗ qA` (stability, RLL 6.4.1, 8.2.8) and `p = π_A : qA → A` (J. Cuntz, K-Theory 1 (1987),
§1).

* `eq_zero_of_comp_eq_zero_of_surjective`;
* `ExtSS.boundaryZero_toExt_comap`, `ExtSS.boundaryOne_toExt_comap`;
* `ExtSSCuntzData.boundaryZero_act_eq_zero`, `ExtSSCuntzData.boundaryOne_act_eq_zero`;
* `ExtSSCuntzData.toExtKKAction_preservesNull`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

section Vanish

variable {M N Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]

/-- A homomorphism that vanishes after precomposition with a surjection vanishes. -/
theorem eq_zero_of_comp_eq_zero_of_surjective {f : M →+ N} (hf : Function.Surjective f)
    {g : N →+ Q} (h : g.comp f = 0) : g = 0 :=
  AddMonoidHom.ext fun y => by
    obtain ⟨w, rfl⟩ := hf y
    exact DFunLike.congr_fun h w

end Vanish

section Semisplit

variable {S T : Type} [NonUnitalCStarAlgebra S] [NonUnitalCStarAlgebra T]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The index map of the underlying `Ext` class is natural along `ExtSS.comap`. -/
theorem ExtSS.boundaryZero_toExt_comap (f : S →⋆ₙₐ[ℂ] T) (η : ExtSS T J) :
    ExtGroup.boundaryZero S J (ExtSS.toExt (ExtSS.comap f η)) =
      (ExtGroup.boundaryZero T J (ExtSS.toExt η)).comp (KZeroN.map f) := by
  rw [ExtSS.toExt_comap_apply]
  exact ExtGroup.boundaryZero_comap f (ExtSS.toExt η)

/-- The exponential map of the underlying `Ext` class is natural along `ExtSS.comap`. -/
theorem ExtSS.boundaryOne_toExt_comap (f : S →⋆ₙₐ[ℂ] T) (η : ExtSS T J) :
    ExtGroup.boundaryOne S J (ExtSS.toExt (ExtSS.comap f η)) =
      (ExtGroup.boundaryOne T J (ExtSS.toExt η)).comp (KOneN.map f) := by
  rw [ExtSS.toExt_comap_apply]
  exact ExtGroup.boundaryOne_comap f (ExtSS.toExt η)

end Semisplit

section Cuntz

variable {F : TWWKK.StableFunctor} {P : SepCStarAlgebra.{0} → Prop}
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

namespace ExtSSCuntzData

variable (D : ExtSSCuntzData F P J) {A B : SepCStarAlgebra.{0}}

/-- If `∂₀ ξ = 0` and `c_*` is onto `K₀(F B)`, then `∂₀ (e_B ξ) = 0`. -/
theorem boundaryZero_eEquiv_eq_zero (hc : Function.Surjective (KZeroN.map (D.c B)))
    (hB : P B) {ξ : ExtGroup B J} (hξ : ExtGroup.boundaryZero B J ξ = 0) :
    ExtGroup.boundaryZero (F.obj B) J (ExtSS.toExt (D.eEquiv hB ξ)) = 0 := by
  refine eq_zero_of_comp_eq_zero_of_surjective hc ?_
  rw [← ExtSS.boundaryZero_toExt_comap (D.c B) (D.eEquiv hB ξ), D.c_eEquiv hB ξ,
    ExtSS.boundaryZero_toExt_comap (D.p B), D.toExt_epsEquiv_symm hB ξ, hξ,
    AddMonoidHom.zero_comp]

/-- If `∂₁ ξ = 0` and `c_*` is onto `K₁(F B)`, then `∂₁ (e_B ξ) = 0`. -/
theorem boundaryOne_eEquiv_eq_zero (hc : Function.Surjective (KOneN.map (D.c B)))
    (hB : P B) {ξ : ExtGroup B J} (hξ : ExtGroup.boundaryOne B J ξ = 0) :
    ExtGroup.boundaryOne (F.obj B) J (ExtSS.toExt (D.eEquiv hB ξ)) = 0 := by
  refine eq_zero_of_comp_eq_zero_of_surjective hc ?_
  rw [← ExtSS.boundaryOne_toExt_comap (D.c B) (D.eEquiv hB ξ), D.c_eEquiv hB ξ,
    ExtSS.boundaryOne_toExt_comap (D.p B), D.toExt_epsEquiv_symm hB ξ, hξ,
    AddMonoidHom.zero_comp]

/-- **The action preserves vanishing index maps**, when `p_*` and `c_*` are onto on `K₀`. -/
theorem boundaryZero_act_eq_zero (hp : Function.Surjective (KZeroN.map (D.p A)))
    (hc : Function.Surjective (KZeroN.map (D.c B))) (hA : P A) (hB : P B)
    (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) {ξ : ExtGroup B J}
    (hξ : ExtGroup.boundaryZero B J ξ = 0) :
    ExtGroup.boundaryZero A J (D.act hA hB x ξ) = 0 := by
  obtain ⟨f, -, hf⟩ := D.exists_pullClass_eq x
  have h1 : ExtGroup.boundaryZero (F.obj A) J
      (ExtSS.toExt (D.pullClass x (D.eEquiv hB ξ))) = 0 := by
    rw [hf, ExtSS.boundaryZero_toExt_comap f, D.boundaryZero_eEquiv_eq_zero hc hB hξ,
      AddMonoidHom.zero_comp]
  refine eq_zero_of_comp_eq_zero_of_surjective hp ?_
  rw [← D.toExt_epsEquiv_symm hA (D.act hA hB x ξ),
    ← ExtSS.boundaryZero_toExt_comap (D.p A) ((D.epsEquiv hA).symm (D.act hA hB x ξ)),
    D.act_spec hA hB x ξ, ExtSS.boundaryZero_toExt_comap (D.c A), h1, AddMonoidHom.zero_comp]

/-- **The action preserves vanishing exponential maps**, when `p_*` and `c_*` are onto on
`K₁`. -/
theorem boundaryOne_act_eq_zero (hp : Function.Surjective (KOneN.map (D.p A)))
    (hc : Function.Surjective (KOneN.map (D.c B))) (hA : P A) (hB : P B)
    (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) {ξ : ExtGroup B J}
    (hξ : ExtGroup.boundaryOne B J ξ = 0) :
    ExtGroup.boundaryOne A J (D.act hA hB x ξ) = 0 := by
  obtain ⟨f, -, hf⟩ := D.exists_pullClass_eq x
  have h1 : ExtGroup.boundaryOne (F.obj A) J
      (ExtSS.toExt (D.pullClass x (D.eEquiv hB ξ))) = 0 := by
    rw [hf, ExtSS.boundaryOne_toExt_comap f, D.boundaryOne_eEquiv_eq_zero hc hB hξ,
      AddMonoidHom.zero_comp]
  refine eq_zero_of_comp_eq_zero_of_surjective hp ?_
  rw [← D.toExt_epsEquiv_symm hA (D.act hA hB x ξ),
    ← ExtSS.boundaryOne_toExt_comap (D.p A) ((D.epsEquiv hA).symm (D.act hA hB x ξ)),
    D.act_spec hA hB x ξ, ExtSS.boundaryOne_toExt_comap (D.c A), h1, AddMonoidHom.zero_comp]

/-- **The Cuntz-picture action preserves "both boundary maps vanish"**, when the legs `p` and
`c` of the zigzag are onto on `K_*`. -/
theorem toExtKKAction_preservesNull [∀ A B : SepCStarAlgebra.{0}, AddCommGroup (F.Hom A B)]
    (hp₀ : ∀ A : SepCStarAlgebra.{0}, Function.Surjective (KZeroN.map (D.p A)))
    (hp₁ : ∀ A : SepCStarAlgebra.{0}, Function.Surjective (KOneN.map (D.p A)))
    (hc₀ : ∀ A : SepCStarAlgebra.{0}, Function.Surjective (KZeroN.map (D.c A)))
    (hc₁ : ∀ A : SepCStarAlgebra.{0}, Function.Surjective (KOneN.map (D.c A))) :
    D.toExtKKAction.PreservesNull
      (fun A ξ => ExtGroup.boundaryZero A J ξ = 0 ∧ ExtGroup.boundaryOne A J ξ = 0) := by
  intro A B hA hB x ξ hξ
  have h0 : ExtGroup.boundaryZero B J ξ = 0 := hξ.1
  have h1 : ExtGroup.boundaryOne B J ξ = 0 := hξ.2
  refine ⟨?_, ?_⟩
  · show ExtGroup.boundaryZero A J (D.act hA hB x ξ) = 0
    exact D.boundaryZero_act_eq_zero (hp₀ A) (hc₀ B) hA hB x h0
  · show ExtGroup.boundaryOne A J (D.act hA hB x ξ) = 0
    exact D.boundaryOne_act_eq_zero (hp₁ A) (hc₁ B) hA hB x h1

end ExtSSCuntzData

end Cuntz

end GroupApproximation.Full.TWWSchafhauser
