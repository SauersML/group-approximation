import GroupApproximation.Sofic.LiteralAffineCongruenceAvatarBlueprint

/-!
# The literal defect ties cannot be `C'(1/8)` and aperiodic

The two defect ties chosen by `LiteralAffineCongruenceAvatarBlueprint` repeat
their two expanded defect words with multiplicities `(3,2)` and `(2,4)`.
If the relators are not proper powers, two occurrences give genuine pieces.
The two resulting `C'(1/8)` inequalities are arithmetically incompatible.

This is an internal no-go theorem for the current avatar family.  It does not
rule out other tying words or other router constructions.
-/

namespace GroupApproximation
namespace AvatarDefectTieNoGo

open SmallCancellationRouter
open BespokeRouter
open BespokeRouter.AvatarWordFamily

/-- The first literal defect tie, abstracted over the two expanded defect
words. -/
def firstTie (T₀ T₁ : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  [((0 : Fin 2), true)] ++ T₀ ++ T₁ ++ T₀ ++ T₀ ++ T₁

/-- The second literal defect tie. -/
def secondTie (T₀ T₁ : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  [((1 : Fin 2), true)] ++ T₁ ++ T₀ ++ T₁ ++ T₁ ++ T₀ ++ T₁

/-- The repeated `T₀` in the first tie is a piece unless that tie is a
proper power. -/
theorem firstTie_isPiece {R : Set (List (Fin 2 × Bool))}
    {T₀ T₁ : List (Fin 2 × Bool)} (hT₀ : T₀ ≠ [])
    (hr : firstTie T₀ T₁ ∈ R)
    (hnpp : BespokeRouter.NoProperPower R) :
    IsPiece (symmetrization R) T₀ := by
  let r := firstTie T₀ T₁
  have hrS : r ∈ symmetrization R := subset_symmetrization R hr
  have hpos : 0 < T₀.length + T₁.length := by
    have : 0 < T₀.length := List.length_pos.mpr hT₀
    omega
  have hshift : T₀.length + T₁.length < r.length := by
    simp only [r, firstTie, List.length_append, List.length_singleton]
    omega
  have hne : r.rotate 1 ≠ r.rotate (1 + (T₀.length + T₁.length)) := by
    intro h
    apply hnpp r hr
    exact PeriodicOverlap.isProperPower_of_rotate_eq_rotate hpos hshift h.symm
  have hrot₁ :
      r.rotate 1 = (T₀ ++ T₁ ++ T₀ ++ T₀ ++ T₁) ++
        [((0 : Fin 2), true)] := by
    simpa only [r, firstTie, List.length_singleton] using
      (List.rotate_append_length_eq [((0 : Fin 2), true)]
        (T₀ ++ T₁ ++ T₀ ++ T₀ ++ T₁))
  have hrot₂ :
      r.rotate (1 + (T₀.length + T₁.length)) =
        (T₀ ++ T₀ ++ T₁) ++ ([((0 : Fin 2), true)] ++ T₀ ++ T₁) := by
    have h := List.rotate_append_length_eq
      ([((0 : Fin 2), true)] ++ T₀ ++ T₁) (T₀ ++ T₀ ++ T₁)
    simpa only [r, firstTie, List.length_append, List.length_singleton,
      List.append_assoc] using h
  refine ⟨r.rotate 1, rotate_mem_symmetrization hrS 1,
    r.rotate (1 + (T₀.length + T₁.length)),
    rotate_mem_symmetrization hrS _, hne, ?_, ?_⟩
  · rw [hrot₁]
    exact List.prefix_append _ _
  · rw [hrot₂]
    exact List.prefix_append _ _

/-- The repeated `T₁` in the second tie is likewise a piece. -/
theorem secondTie_isPiece {R : Set (List (Fin 2 × Bool))}
    {T₀ T₁ : List (Fin 2 × Bool)} (hT₁ : T₁ ≠ [])
    (hr : secondTie T₀ T₁ ∈ R)
    (hnpp : BespokeRouter.NoProperPower R) :
    IsPiece (symmetrization R) T₁ := by
  let r := secondTie T₀ T₁
  have hrS : r ∈ symmetrization R := subset_symmetrization R hr
  have hpos : 0 < T₁.length + T₀.length := by
    have : 0 < T₁.length := List.length_pos.mpr hT₁
    omega
  have hshift : T₁.length + T₀.length < r.length := by
    simp only [r, secondTie, List.length_append, List.length_singleton]
    omega
  have hne : r.rotate 1 ≠ r.rotate (1 + (T₁.length + T₀.length)) := by
    intro h
    apply hnpp r hr
    exact PeriodicOverlap.isProperPower_of_rotate_eq_rotate hpos hshift h.symm
  have hrot₁ :
      r.rotate 1 = (T₁ ++ T₀ ++ T₁ ++ T₁ ++ T₀ ++ T₁) ++
        [((1 : Fin 2), true)] := by
    simpa only [r, secondTie, List.length_singleton] using
      (List.rotate_append_length_eq [((1 : Fin 2), true)]
        (T₁ ++ T₀ ++ T₁ ++ T₁ ++ T₀ ++ T₁))
  have hrot₂ :
      r.rotate (1 + (T₁.length + T₀.length)) =
        (T₁ ++ T₁ ++ T₀ ++ T₁) ++
          ([((1 : Fin 2), true)] ++ T₁ ++ T₀) := by
    have h := List.rotate_append_length_eq
      ([((1 : Fin 2), true)] ++ T₁ ++ T₀)
      (T₁ ++ T₁ ++ T₀ ++ T₁)
    simpa only [r, secondTie, List.length_append, List.length_singleton,
      List.append_assoc] using h
  refine ⟨r.rotate 1, rotate_mem_symmetrization hrS 1,
    r.rotate (1 + (T₁.length + T₀.length)),
    rotate_mem_symmetrization hrS _, hne, ?_, ?_⟩
  · rw [hrot₁]
    exact List.prefix_append _ _
  · rw [hrot₂]
    exact List.prefix_append _ _

/-- **The multiplicity obstruction.**  No relator family containing these two
ties is both aperiodic and `C'(1/8)`. -/
theorem not_noProperPower_and_metric_eighth
    {R : Set (List (Fin 2 × Bool))} {T₀ T₁ : List (Fin 2 × Bool)}
    (hT₀ : T₀ ≠ []) (hT₁ : T₁ ≠ [])
    (hr₀ : firstTie T₀ T₁ ∈ R) (hr₁ : secondTie T₀ T₁ ∈ R) :
    ¬ (BespokeRouter.NoProperPower R ∧ MetricSmallCancellation R (1 / 8)) := by
  rintro ⟨hnpp, hmetric⟩
  have hp₀ := firstTie_isPiece hT₀ hr₀ hnpp
  have hp₁ := secondTie_isPiece hT₁ hr₁ hnpp
  have hr₀S : (firstTie T₀ T₁).rotate 1 ∈ symmetrization R :=
    rotate_mem_symmetrization (subset_symmetrization R hr₀) 1
  have hr₁S : (secondTie T₀ T₁).rotate 1 ∈ symmetrization R :=
    rotate_mem_symmetrization (subset_symmetrization R hr₁) 1
  have hpre₀ : T₀ <+: (firstTie T₀ T₁).rotate 1 := by
    rw [show (firstTie T₀ T₁).rotate 1 =
      (T₀ ++ T₁ ++ T₀ ++ T₀ ++ T₁) ++ [((0 : Fin 2), true)] by
        simpa only [firstTie, List.length_singleton] using
          (List.rotate_append_length_eq [((0 : Fin 2), true)]
            (T₀ ++ T₁ ++ T₀ ++ T₀ ++ T₁))]
    exact List.prefix_append _ _
  have hpre₁ : T₁ <+: (secondTie T₀ T₁).rotate 1 := by
    rw [show (secondTie T₀ T₁).rotate 1 =
      (T₁ ++ T₀ ++ T₁ ++ T₁ ++ T₀ ++ T₁) ++ [((1 : Fin 2), true)] by
        simpa only [secondTie, List.length_singleton] using
          (List.rotate_append_length_eq [((1 : Fin 2), true)]
            (T₁ ++ T₀ ++ T₁ ++ T₁ ++ T₀ ++ T₁))]
    exact List.prefix_append _ _
  have hq₀ := hmetric T₀ hp₀ ((firstTie T₀ T₁).rotate 1) hr₀S hpre₀
  have hq₁ := hmetric T₁ hp₁ ((secondTie T₀ T₁).rotate 1) hr₁S hpre₁
  rw [List.length_rotate] at hq₀ hq₁
  have hnat₀ : 8 * T₀.length < (firstTie T₀ T₁).length := by
    exact_mod_cast (show (8 : ℚ) * (T₀.length : ℚ) <
      ((firstTie T₀ T₁).length : ℚ) by linarith)
  have hnat₁ : 8 * T₁.length < (secondTie T₀ T₁).length := by
    exact_mod_cast (show (8 : ℚ) * (T₁.length : ℚ) <
      ((secondTie T₀ T₁).length : ℚ) by linarith)
  have hlen₀ : 0 < T₀.length := List.length_pos.mpr hT₀
  simp only [firstTie, secondTie, List.length_append, List.length_singleton] at
    hnat₀ hnat₁
  omega

open LiteralAffineCongruenceAvatarBlueprint

/-- The two expanded defect words in the literal blueprint are nonempty. -/
theorem literal_defectAvatarWord_ne_nil (i : Fin 2) :
    blueprint.defectAvatarWord i ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [length_avatarSubst_eq blueprint.srcAvatarWord blueprint.avatarLength
    blueprint.length_srcAvatarWord]
  have hb := blueprint_basis_ne_nil i
  have hS := blueprint.sixteen_le_avatarLength
  omega

/-- The first literal defect tie has the abstract multiplicity pattern above. -/
theorem literal_defectTieWord_zero :
    blueprint.defectTieWord 0 =
      firstTie (blueprint.defectAvatarWord 0) (blueprint.defectAvatarWord 1) := by
  rfl

/-- The second literal defect tie has the second multiplicity pattern. -/
theorem literal_defectTieWord_one :
    blueprint.defectTieWord 1 =
      secondTie (blueprint.defectAvatarWord 0) (blueprint.defectAvatarWord 1) := by
  rfl

/-- **The current literal avatar blueprint has no obligations witness.** -/
theorem not_literal_blueprint_obligations : ¬ blueprint.Obligations := by
  intro H
  apply not_noProperPower_and_metric_eighth
    (literal_defectAvatarWord_ne_nil 0) (literal_defectAvatarWord_ne_nil 1)
    (R := blueprint.relators)
  · rw [← literal_defectTieWord_zero]
    exact blueprint.mem_relators_defectTie 0
  · rw [← literal_defectTieWord_one]
    exact blueprint.mem_relators_defectTie 1
  · exact ⟨H.relators_noProperPower, H.metric_eighth⟩

end AvatarDefectTieNoGo
end GroupApproximation
