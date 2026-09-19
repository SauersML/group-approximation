import GroupApproximation.Manuscript.NonMF.SimpleInDefect

/-!
# The normal-generation step in the torsion-free theorem

This is the sentence in the proof of the torsion-free theorem that passes from
`φ(N) = Q`, where `N` is the normal closure of the Fournier--Facio factor `S`,
to

`⟪ρ(S)⟫ = ρ(N) = Gbar`

and then uses `lem:commutator-in-defect` and normality of the printed defect to
deduce `𝔇_Gbar(ρ(Γ)) = Gbar`.  The target `Gbar` is represented literally as
the range of the arbitrary homomorphism `r : Q → M`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF

universe u v w

open PrintedFournierFacioData

variable {E : Type u} {Q : Type v} {M : Type w}
  [Group E] [Group Q] [Group M]

/-- **The normal-generation sentence in the proof of the torsion-free
theorem.**  If `φ` maps the normal closure of `S` onto `Q`, then after any map
`r : Q → M` the composite `ρ`, regarded as a surjection onto `r.range`, maps
that normal closure onto all of `r.range`.  Equivalently, `ρ(S)` normally
generates `r.range`; since the commutator-in-defect lemma puts `ρ(S)` in the
normal printed defect, that defect is the whole range. -/
theorem normalClosure_image_eq_range_and_printedDefect_eq_top
    (F : PrintedFournierFacioData E) (φ : E →* Q) (r : Q →* M)
    (hφN : (Subgroup.normalClosure (F.conjFactor : Set E)).map φ = ⊤) :
    let ρ : E →* r.range := r.rangeRestrict.comp φ
    (Subgroup.normalClosure (F.conjFactor : Set E)).map ρ = ⊤ ∧
      Subgroup.normalClosure (F.conjFactor.map ρ : Set r.range) = ⊤ ∧
        OneSidedMFRadical.printedDefect (F.core.map ρ) = ⊤ := by
  let ρ : E →* r.range := r.rangeRestrict.comp φ
  have hφ : Function.Surjective φ := by
    intro q
    have hq : q ∈ (⊤ : Subgroup Q) := trivial
    rw [← hφN] at hq
    obtain ⟨x, _hx, hxeq⟩ := hq
    exact ⟨x, hxeq⟩
  have hρ : Function.Surjective ρ :=
    r.rangeRestrict_surjective.comp hφ
  have hmap :
      (Subgroup.normalClosure (F.conjFactor : Set E)).map ρ = ⊤ := by
    change (Subgroup.normalClosure (F.conjFactor : Set E)).map
      (r.rangeRestrict.comp φ) = ⊤
    rw [← Subgroup.map_map, hφN,
      Subgroup.map_top_of_surjective r.rangeRestrict r.rangeRestrict_surjective]
  have hnormal :
      Subgroup.normalClosure (F.conjFactor.map ρ : Set r.range) = ⊤ := by
    have hset : (F.conjFactor.map ρ : Set r.range) =
        ρ '' (F.conjFactor : Set E) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hset, ← Subgroup.map_normalClosure (F.conjFactor : Set E) ρ hρ]
    exact hmap
  have hfactor : F.conjFactor.map ρ ≤
      OneSidedMFRadical.printedDefect (F.core.map ρ) :=
    F.map_conjFactor_le_printedDefect ρ
  have hclosure : Subgroup.normalClosure
      (F.conjFactor.map ρ : Set r.range) ≤
        OneSidedMFRadical.printedDefect (F.core.map ρ) :=
    Subgroup.normalClosure_le_normal hfactor
  refine ⟨hmap, hnormal, ?_⟩
  apply top_unique
  rw [← hnormal]
  exact hclosure

end NonMF
end Manuscript
end GroupApproximation

#print axioms GroupApproximation.Manuscript.NonMF.normalClosure_image_eq_range_and_printedDefect_eq_top
