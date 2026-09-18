import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalZero

/-!
# Half-exactness of non-unital K-theory: the unitized maps

Lane `TWWSch3d3-1C`, work order `WO-3d3-1C`, for `thm:fixed-radical-membership`
(`non_mf_group_notes.tex`, l.1376--1378). Consider an exact sequence `J → A → B` of
non-unital C⋆-algebras, with `ι : J → A` injective, `π : A → B` surjective and
`ker π = range ι`. This file collects the facts about the unitized maps
`ι⁺ : J⁺ → A⁺` and `π⁺ : A⁺ → B⁺` that the half-exactness of `K₀` and `K₁` needs
(M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*,
Propositions 4.3.3 and 8.2.4).

* `comp_eq_zero_of_exact`: `π ∘ ι = 0`;
* `snd_starMap`: the non-scalar part of `φ⁺ a` is `φ a.snd`;
* `exists_starMap_eq_of_starMap_eq_algebraMap`: an element of `A⁺` whose image under `π⁺` is
  a scalar lies in the image of `ι⁺`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

section Unitized

variable {J A B : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] {ι : J →⋆ₙₐ[ℂ] A} {π : A →⋆ₙₐ[ℂ] B}

/-- The two maps of an exact pair compose to zero. -/
theorem comp_eq_zero_of_exact (hex : ∀ a, π a = 0 ↔ a ∈ Set.range ι) : π.comp ι = 0 :=
  NonUnitalStarAlgHom.ext fun j => by
    rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.zero_apply]
    exact (hex (ι j)).mpr ⟨j, rfl⟩

/-- The non-scalar part of `φ⁺ a` is `φ a.snd`. -/
theorem snd_starMap (φ : A →⋆ₙₐ[ℂ] B) (a : Unitization ℂ A) :
    (Unitization.starMap φ a).snd = φ a.snd := by
  show ((Unitization.inl a.fst : Unitization ℂ B) + (φ a.snd : Unitization ℂ B)).snd = φ a.snd
  rw [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

/-- **Lifting along an exact pair.** If `π⁺ a` is a scalar, then `a` lies in the image of
`ι⁺`. -/
theorem exists_starMap_eq_of_starMap_eq_algebraMap (hex : ∀ a, π a = 0 ↔ a ∈ Set.range ι)
    {a : Unitization ℂ A} {c : ℂ}
    (h : Unitization.starMap π a = algebraMap ℂ (Unitization ℂ B) c) :
    ∃ x : Unitization ℂ J, Unitization.starMap ι x = a := by
  have hs : π a.snd = 0 := by
    rw [← snd_starMap π a, h, Unitization.algebraMap_eq_inl, Unitization.snd_inl]
  obtain ⟨j, hj⟩ := (hex a.snd).mp hs
  refine ⟨(Unitization.inl a.fst : Unitization ℂ J) + (Unitization.inr j : Unitization ℂ J), ?_⟩
  rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr, hj,
    Unitization.algebraMap_eq_inl]
  exact Unitization.inl_fst_add_inr_snd_eq a

end Unitized

end

end TWWSchafhauser
end Full
end GroupApproximation
