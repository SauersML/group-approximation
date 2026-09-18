import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Qalg

/-!
# Naturality of Cuntz's projection `π_A : qA → A`

Lane `TWWSch3d3-3A`, work order `WO-TWWSchafhauser-3d3-3A`. The manuscript statement is
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). This file gives the
naturality of the left leg `p = π` of the zigzag `A ←π— qA —c→ 𝒦 ⊗ qA`, which the action
assembly (`ExtSSCuntzData.p_natural`) needs. The reference is J. Cuntz, *A new look at
KK-theory*, K-Theory 1 (1987), §1.

* `unitization_snd_starMap`: `(φ̃ x).snd = φ x.snd` on the unitization.
* `starMap_comp_piPre`: `φ̃ ∘ π̃_A = π̃_B ∘ (φ * φ)` on the full free product.
* `qalg_pi_natural`: `φ ∘ π_A = π_B ∘ qφ`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u

section PiNatural

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- `Unitization.starMap φ` acts by `φ` on the non-unital part. -/
theorem unitization_snd_starMap (φ : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (Unitization.starMap φ x).snd = φ x.snd := by
  conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
  rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr, Unitization.snd_add,
    Unitization.algebraMap_eq_inl, Unitization.snd_inl, Unitization.snd_inr, zero_add]

/-- The unital extension of `π` is natural: `φ̃ ∘ π̃_A = π̃_B ∘ (φ * φ)`. -/
theorem starMap_comp_piPre (φ : A →⋆ₙₐ[ℂ] B) :
    (Unitization.starMap φ).comp (TWWKK.Qalg.piPre A) =
      (TWWKK.Qalg.piPre B).comp (TWWKK.FreeProd.freeMap φ) :=
  TWWKK.FreeProd.hom_ext
    (fun a => ((congrArg (Unitization.starMap φ) (TWWKK.Qalg.piPre_ι₁ a)).trans
        (Unitization.starMap_inr φ a)).trans
      ((TWWKK.Qalg.piPre_ι₁ (φ a)).symm.trans
        (congrArg (TWWKK.Qalg.piPre B) (TWWKK.FreeProd.freeMap_ι₁ φ a)).symm))
    (fun a => ((congrArg (Unitization.starMap φ) (TWWKK.Qalg.piPre_ι₂ a)).trans
        (map_zero (Unitization.starMap φ))).trans
      ((TWWKK.Qalg.piPre_ι₂ (φ a)).symm.trans
        (congrArg (TWWKK.Qalg.piPre B) (TWWKK.FreeProd.freeMap_ι₂ φ a)).symm))

/-- **Naturality of Cuntz's projection**: `φ ∘ π_A = π_B ∘ qφ`. -/
theorem qalg_pi_natural (φ : A →⋆ₙₐ[ℂ] B) :
    φ.comp (TWWKK.Qalg.pi A) = (TWWKK.Qalg.pi B).comp (TWWKK.Qalg.map φ) :=
  NonUnitalStarAlgHom.ext fun x => by
    show φ (TWWKK.Qalg.pi A x) = TWWKK.Qalg.pi B (TWWKK.Qalg.map φ x)
    rw [TWWKK.Qalg.pi_apply, TWWKK.Qalg.pi_apply, TWWKK.Qalg.coe_map,
      ← unitization_snd_starMap φ]
    exact congrArg Unitization.snd
      (DFunLike.congr_fun (starMap_comp_piPre φ) (x : TWWKK.FreeProd.FreeUnital A))

end PiNatural

end GroupApproximation.Full.TWWSchafhauser
