import GroupApproximation.KunThom.CountingEndgamePropsOneSided

/-!
# The selected objects of a bundled relative cluster functor

The finite core of the producer `hcounting`.  In Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222v3, §4, tex lines 1218–1276) an object `i` is good when `i` and its
image `ā i` under the bisection are matched, the matches `π i` and `π (ā i)` have clean
orbits, and the arrow counts at `i` and `ā i` satisfy the squared ratio bounds.  A good
object is the image of a selected object of `CountingEndgame.selected`, so the lift
`RelativeClusterFunctor.exists_bisection_lift` carries its arrow.

* `ratios_of_sqRatio`: real arithmetic.  The squared ratio bound for the arrow count,
  isotropy monotonicity and cleanliness bound the orbit ratio by `1 + 16η` and the
  isotropy ratio by `(1 + 16η) / (1 - ζ)`.
* `targetChoice`, `targetChoice_spec`: a preimage of the target of the bisection when
  one exists.
* `RelativeClusterFunctor.lift_obj`: the functor followed by the inclusion of its
  target sends the retained object `π i` to `i`.
* `RelativeClusterFunctor.counts_of_clean`: at a matched object with clean match, the
  orbit of the match loses at most a `ζ` fraction and the isotropy grows.
* `RelativeClusterFunctor.mem_image_selected`: every good object is the image of a
  selected object, once `1 + 16η < 2 (1 - ζ)`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory GroupoidPresentation

universe u v u' v' u'' v''

/-- **Ratios from the squared ratio bound.** -/
theorem ratios_of_sqRatio {oX kX oF kF ζ η : ℝ} (hoX : 0 < oX) (hkX : 0 < kX)
    (hoF : 0 ≤ oF) (hkF : 0 ≤ kF) (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 16)
    (hsq : (1 - 2 * η) ^ 2 * (oF * kF) ≤ (1 + 2 * η) ^ 2 * (oX * kX))
    (hvert : kX ≤ kF) (hclean : (1 - ζ) * oX ≤ oF) :
    oF ≤ (1 + 16 * η) * oX ∧ (1 - ζ) * kF ≤ (1 + 16 * η) * kX := by
  have hb := ArrowCountMedian.le_one_add_mul_of_sq_mul_le (mul_nonneg hoX.le hkX.le) hη hη₁ hsq
  refine ⟨?_, ?_⟩
  · have h₁ : oF * kX ≤ ((1 + 16 * η) * oX) * kX := by
      calc oF * kX ≤ oF * kF := mul_le_mul_of_nonneg_left hvert hoF
        _ ≤ (1 + 16 * η) * (oX * kX) := hb
        _ = ((1 + 16 * η) * oX) * kX := by ring
    exact le_of_mul_le_mul_right h₁ hkX
  · have h₂ : ((1 - ζ) * kF) * oX ≤ ((1 + 16 * η) * kX) * oX := by
      calc ((1 - ζ) * kF) * oX = ((1 - ζ) * oX) * kF := by ring
        _ ≤ oF * kF := mul_le_mul_of_nonneg_right hclean hkF
        _ ≤ (1 + 16 * η) * (oX * kX) := hb
        _ = ((1 + 16 * η) * kX) * oX := by ring
    exact le_of_mul_le_mul_right h₂ hoX

/-- A preimage of the target of the bisection when one exists. -/
noncomputable def targetChoice {C' : Type u'} [Groupoid.{v'} C'] {D : Type u''}
    [Groupoid.{v''} D] (F : C' ⥤ D) (a : FiniteGroupoid.Bisection D) (X : C') : C' := by
  classical
  exact if h : ∃ Y, F.obj Y = a.objEquiv (F.obj X) then Classical.choose h else X

theorem targetChoice_spec {C' : Type u'} [Groupoid.{v'} C'] {D : Type u''}
    [Groupoid.{v''} D] (F : C' ⥤ D) (a : FiniteGroupoid.Bisection D) {X : C'}
    (h : ∃ Y, F.obj Y = a.objEquiv (F.obj X)) :
    F.obj (targetChoice F a X) = a.objEquiv (F.obj X) := by
  unfold targetChoice
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The functor of a bundled relative cluster functor, followed by the inclusion of its
target, sends the retained object `π i` to `i`. -/
theorem RelativeClusterFunctor.lift_obj {I : Type u} {P : GroupoidPresentation.{u, v} I}
    {Rt Mt : Finset I} (𝓕 : P.RelativeClusterFunctor Rt Mt) {i : I} (hi : i ∈ Mt) :
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj
      ⟨⟨𝓕.π i, 𝓕.mapsTo (Finset.mem_coe.mpr hi)⟩⟩ = (⟨i⟩ : P.Obj) := by
  show (⟨(𝓕.F.obj ⟨𝓕.π i, 𝓕.mapsTo (Finset.mem_coe.mpr hi)⟩).1⟩ : P.Obj) = ⟨i⟩
  rw [𝓕.obj_π i hi]

/-- **Counts at a clean match.**  At a matched object `i` whose match has a clean
orbit, `(1 - ζ) |orbit (π i)| ≤ |orbit i|` and `|π i ⟶ π i| ≤ |i ⟶ i|`. -/
theorem RelativeClusterFunctor.counts_of_clean {I : Type u} [Fintype I] [DecidableEq I]
    {P : GroupoidPresentation.{u, v} I} [∀ i j, Finite (P.Rep i j)] {Rt Mt : Finset I}
    (𝓕 : P.RelativeClusterFunctor Rt Mt) {i : I} (hi : i ∈ Mt) {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj) ∩
        (Finset.univ \ Rt).image (Obj.mk (P := P))).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card) :
    (1 - ζ) * ((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card : ℝ) ≤
        (FiniteGroupoid.orbit (⟨i⟩ : P.Obj)).card ∧
      Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩) ≤ Fintype.card ((⟨i⟩ : P.Obj) ⟶ ⟨i⟩) := by
  haveI := 𝓕.faithful
  have hmem : 𝓕.π i ∈ (Rt : Set I) := 𝓕.mapsTo (Finset.mem_coe.mpr hi)
  have hF : Function.Injective
      (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj :=
    (P.restrictInclusionFunctor_obj_injective _).comp 𝓕.toFunctor_obj_injective
  have hsub := orbit_sdiff_image_subset P Rt ⟨⟨𝓕.π i, hmem⟩⟩
  have hclean' : ((FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩) \
      Finset.univ.image (P.restrictInclusionFunctor (Rt : Set I)).obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩)).card := by
    refine le_trans ?_ hclean
    exact_mod_cast Finset.card_le_card hsub
  have horb := mul_card_orbit_le_card_orbit_map_of_clean
    (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) hF ⟨⟨𝓕.π i, hmem⟩⟩ hclean'
  have hvert := card_vertexGroup_le_card_vertexGroup_map
    (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) ⟨⟨𝓕.π i, hmem⟩⟩
  rw [RelativeClusterFunctor.lift_obj 𝓕 hi] at horb hvert
  exact ⟨horb, hvert⟩

/-- **Good objects are selected.**  Let `i` be matched, with `j := ā i` matched, clean
matches `π i` and `π j` at scale `ζ`, and the squared ratio bounds for the arrow counts
at `i` and at `j`.  If `1 + 16η < 2 (1 - ζ)`, then `i` is the image of an object of
`selected (F ⋙ K) a (targetChoice (F ⋙ K) a)`. -/
theorem RelativeClusterFunctor.mem_image_selected {I : Type u} [Fintype I] [DecidableEq I]
    {P : GroupoidPresentation.{u, v} I} [∀ i j, Finite (P.Rep i j)] {Rt Mt : Finset I}
    (𝓕 : P.RelativeClusterFunctor Rt Mt) (a : FiniteGroupoid.Bisection P.Obj) {i : I}
    (hi : i ∈ Mt) (hj : (a.objEquiv ⟨i⟩).val ∈ Mt) {ζ η : ℝ} (hη : 0 ≤ η)
    (hη₁ : η ≤ 1 / 16) (hηζ : 1 + 16 * η < 2 * (1 - ζ))
    (hclean : ((FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj) ∩
        (Finset.univ \ Rt).image (Obj.mk (P := P))).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (⟨𝓕.π i⟩ : P.Obj)).card)
    (hclean' : ((FiniteGroupoid.orbit (⟨𝓕.π (a.objEquiv ⟨i⟩).val⟩ : P.Obj) ∩
        (Finset.univ \ Rt).image (Obj.mk (P := P))).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (⟨𝓕.π (a.objEquiv ⟨i⟩).val⟩ : P.Obj)).card)
    (hsq : (1 - 2 * η) ^ 2 * (ArrowCountMedian.arrowCount (⟨i⟩ : P.Obj) : ℝ) ≤
      (1 + 2 * η) ^ 2 * ArrowCountMedian.arrowCount (⟨𝓕.π i⟩ : P.Obj))
    (hsq' : (1 - 2 * η) ^ 2 *
        (ArrowCountMedian.arrowCount (⟨(a.objEquiv ⟨i⟩).val⟩ : P.Obj) : ℝ) ≤
      (1 + 2 * η) ^ 2 * ArrowCountMedian.arrowCount (⟨𝓕.π (a.objEquiv ⟨i⟩).val⟩ : P.Obj)) :
    i ∈ (selected (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a
        (targetChoice (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a)).image
      (fun X ↦ ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj X).val) := by
  haveI := 𝓕.faithful
  have hζ₁ : ζ < 1 := by linarith
  have hmem : 𝓕.π i ∈ (Rt : Set I) := 𝓕.mapsTo (Finset.mem_coe.mpr hi)
  have hmem' : 𝓕.π (a.objEquiv ⟨i⟩).val ∈ (Rt : Set I) := 𝓕.mapsTo (Finset.mem_coe.mpr hj)
  have hF : Function.Injective
      (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj :=
    (P.restrictInclusionFunctor_obj_injective _).comp 𝓕.toFunctor_obj_injective
  have hX := RelativeClusterFunctor.lift_obj 𝓕 hi
  have hY := RelativeClusterFunctor.lift_obj 𝓕 hj
  -- the target of the selected object
  have hex : ∃ Y, (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj Y =
      a.objEquiv ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩) := by
    refine ⟨⟨⟨𝓕.π (a.objEquiv ⟨i⟩).val, hmem'⟩⟩, ?_⟩
    rw [hY, hX]
  have hsel := targetChoice_spec (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a hex
  have hX' : targetChoice (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a
      ⟨⟨𝓕.π i, hmem⟩⟩ = ⟨⟨𝓕.π (a.objEquiv ⟨i⟩).val, hmem'⟩⟩ := by
    apply hF
    rw [hsel, hY, hX]
  -- counts at i and at j
  obtain ⟨horb, hvert⟩ := RelativeClusterFunctor.counts_of_clean 𝓕 hi hclean
  obtain ⟨horb', hvert'⟩ := RelativeClusterFunctor.counts_of_clean 𝓕 hj hclean'
  have hoX := ArrowCountMedian.card_orbit_pos (⟨𝓕.π i⟩ : P.Obj)
  have hkX := ArrowCountMedian.card_vertexGroup_pos (⟨𝓕.π i⟩ : P.Obj)
  have hoX' := ArrowCountMedian.card_orbit_pos (⟨𝓕.π (a.objEquiv ⟨i⟩).val⟩ : P.Obj)
  have hkX' := ArrowCountMedian.card_vertexGroup_pos (⟨𝓕.π (a.objEquiv ⟨i⟩).val⟩ : P.Obj)
  rw [ArrowCountMedian.arrowCount_cast, ArrowCountMedian.arrowCount_cast] at hsq hsq'
  obtain ⟨hratio, hratiok⟩ := ratios_of_sqRatio hoX hkX (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hη hη₁ hsq (by exact_mod_cast hvert) horb
  obtain ⟨hratio', -⟩ := ratios_of_sqRatio hoX' hkX' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hη hη₁ hsq' (by exact_mod_cast hvert') horb'
  have horbit_eq : FiniteGroupoid.orbit (⟨i⟩ : P.Obj) =
      FiniteGroupoid.orbit (⟨(a.objEquiv ⟨i⟩).val⟩ : P.Obj) :=
    FiniteGroupoid.orbit_eq_of_hom (a.hom ⟨i⟩)
  -- cleanliness at the two retained objects
  have hsub := orbit_sdiff_image_subset P Rt ⟨⟨𝓕.π i, hmem⟩⟩
  have hsub' := orbit_sdiff_image_subset P Rt ⟨⟨𝓕.π (a.objEquiv ⟨i⟩).val, hmem'⟩⟩
  have hcleanJ : ((FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩) \
      Finset.univ.image (P.restrictInclusionFunctor (Rt : Set I)).obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩)).card := by
    refine le_trans ?_ hclean
    exact_mod_cast Finset.card_le_card hsub
  have hcleanJ' : ((FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        (targetChoice (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a
          ⟨⟨𝓕.π i, hmem⟩⟩)) \
      Finset.univ.image (P.restrictInclusionFunctor (Rt : Set I)).obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        (targetChoice (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a
          ⟨⟨𝓕.π i, hmem⟩⟩))).card := by
    rw [hX']
    refine le_trans ?_ hclean'
    exact_mod_cast Finset.card_le_card hsub'
  -- the orbit count
  have hratioF : ((FiniteGroupoid.orbit
      ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩)).card : ℝ) ≤
      (1 + 16 * η) * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        ⟨⟨𝓕.π i, hmem⟩⟩)).card := by
    rw [hX]
    exact hratio
  have hratioF' : ((FiniteGroupoid.orbit
      ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩)).card : ℝ) ≤
      (1 + 16 * η) * (FiniteGroupoid.orbit ((P.restrictInclusionFunctor (Rt : Set I)).obj
        (targetChoice (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) a
          ⟨⟨𝓕.π i, hmem⟩⟩))).card := by
    rw [hX, hX', horbit_eq]
    exact hratio'
  have hρ : 0 < 1 + 16 * η := by linarith
  have horbitCount := card_orbit_lt_add_of_clean (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) hρ hηζ hcleanJ hcleanJ'
    hratioF hratioF'
  -- the isotropy index
  have hρk : (1 + 16 * η) / (1 - ζ) < 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hratioK : (Fintype.card
      ((𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩ ⟶
        (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩) : ℝ) ≤
      (1 + 16 * η) / (1 - ζ) * Fintype.card
        ((P.restrictInclusionFunctor (Rt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩ ⟶
          (P.restrictInclusionFunctor (Rt : Set I)).obj ⟨⟨𝓕.π i, hmem⟩⟩) := by
    rw [hX, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    show (Fintype.card ((⟨i⟩ : P.Obj) ⟶ ⟨i⟩) : ℝ) * (1 - ζ) ≤
      (1 + 16 * η) * Fintype.card ((⟨𝓕.π i⟩ : P.Obj) ⟶ ⟨𝓕.π i⟩)
    linarith
  have hvertexCount := card_vertexGroup_lt_two_mul_of_ratio
    (P.restrictInclusionFunctor (Rt : Set I))
    (𝓕.F.toFunctor ⋙ P.restrictInclusionFunctor (Mt : Set I)) ⟨⟨𝓕.π i, hmem⟩⟩ hρk hratioK
  refine Finset.mem_image.mpr ⟨⟨⟨𝓕.π i, hmem⟩⟩, ?_, congrArg Obj.val hX⟩
  exact (mem_selected _ a _ _).mpr ⟨hsel, horbitCount, hvertexCount⟩

end CountingEndgame
end GroupApproximation
