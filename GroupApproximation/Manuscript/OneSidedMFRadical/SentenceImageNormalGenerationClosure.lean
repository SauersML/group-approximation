import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# The image normal-generation route in defect saturation

This file exposes the inclusions used in census row 199 before the mapped
printed defect is identified with the whole target group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

section

variable {G Q : Type*} [Group G] [Group Q]

/-- The functoriality equation sends the simple subgroup already contained in
`D_G(L)` into `D_Q(f(L))`.  This is the first assertion in census row 199. -/
theorem manuscriptSimpleImageLeMappedPrintedDefect
    (f : G →* Q) (L S : Subgroup G)
    (hSD : S ≤ printedDefect L) :
    S.map f ≤ printedDefect (L.map f) :=
  (Subgroup.map_mono hSD).trans (map_printedDefect_le f L)

/-- Normality of the mapped printed defect upgrades the image inclusion to
containment of the normal closure of `f(S)`. -/
theorem manuscriptNormalClosureSimpleImageLeMappedPrintedDefect
    (f : G →* Q) (L S : Subgroup G)
    (hSD : S ≤ printedDefect L) :
    Subgroup.normalClosure (S.map f : Set Q) ≤
      printedDefect (L.map f) :=
  Subgroup.normalClosure_le_normal
    (manuscriptSimpleImageLeMappedPrintedDefect f L S hSD)

/-- **Sentence-census row 199.**  The hypotheses are exactly the printed
ones (`f` onto, `S ≤ 𝔇_G(L)`, `f(S)` normally generating `Q`; simplicity of
`S` and nontriviality of `f(S)` are not assumed), while the conclusion
exposes in order the image inclusion, normal closure containment, and the
resulting equality with `Q`. -/
theorem manuscriptSimpleImageNormalGenerationRoute
    (f : G →* Q) (_hf : Function.Surjective f)
    (L S : Subgroup G)
    (hSD : S ≤ printedDefect L)
    (hgen : Subgroup.normalClosure (S.map f : Set Q) = ⊤) :
    S.map f ≤ printedDefect (L.map f) ∧
      Subgroup.normalClosure (S.map f : Set Q) ≤
        printedDefect (L.map f) ∧
      printedDefect (L.map f) = ⊤ := by
  have hmap := manuscriptSimpleImageLeMappedPrintedDefect f L S hSD
  have hclosure :=
    manuscriptNormalClosureSimpleImageLeMappedPrintedDefect f L S hSD
  refine ⟨hmap, hclosure, ?_⟩
  apply top_unique
  rw [← hgen]
  exact hclosure

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
