import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoints
import GroupApproximation.Leavitt.DiagonalNormalExtraction
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.PropertyTT.RingHypotheses

/-!
# Rank-four simplicity: exact reductions

This module proves Proposition `prop:simple` for
`H = EL₄(L_{𝔽₂}(1,2))`.  Every elementary root with a unit-sandwiched
coefficient normally generates `H`, and over `L_{𝔽₂}(1,2)` every nonzero
coefficient is unit-sandwiched, so every nonzero root normally generates.
`DiagonalNormalExtraction.rootDetection_of_leavittFamily` supplies root
detection by an exhaustive diagonal/zero-inverse/dense-entry split.  Leavitt
coefficient separation handles the dense case, while trivial central units
handle the diagonal case.

Both inputs ask only for three indices, so nothing here is specific to rank
four beyond the index type; the superseded rank-twelve development used the
same two theorems.

The canonical level ideal and lower half of Preusser's sandwich are also
formalized in `CongruenceSubgroups`; below they give the independent
unconditional fact that every proper normal subgroup has level zero.  The
upper Preusser inclusion remains absent as a literal formalization of the
manuscript's cited route, but it is no longer needed for simplicity because
the direct extraction proof produces a nonzero root.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankFourEndpoint

/-- Every nonzero coefficient of the manuscript's ring admits a unit
sandwich; this is the one ring fact both branches of the case split use. -/
theorem coefficient_unit_sandwich (x : R) (hx : x ≠ 0) :
    ∃ a b : R, a * x * b = 1 :=
  BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx

/-- The diagonal branch of root detection: a normal subgroup containing any
nonidentity diagonal matrix is already all of `H`.  The dense branch is closed
separately and the exhaustive combination appears below. -/
theorem normal_eq_top_of_nonidentity_diagonal_mem
    (N : Subgroup H) (hN : N.Normal)
    {g : H} (hg : g ∈ N) (hgne : g ≠ 1)
    (hdiag : ∀ p q : Fin 4, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    N = ⊤ := by
  letI : N.Normal := hN
  exact normal_eq_top_of_diagonal_mem three_le_card
    coefficient_unit_sandwich
    BinaryLeavitt.central_units_trivial N hg hgne hdiag

/-- At rank four, an elementary root is trivial exactly when its coefficient
is zero. -/
theorem elementaryRoot_eq_one_iff (i j : Fin 4) (hij : i ≠ j) (a : R) :
    elementaryRoot i j hij a = 1 ↔ a = 0 := by
  change elGen i j hij a = 1 ↔ a = 0
  exact LeavittMark.elGen_eq_one_iff i j hij a

/-- Any normal subgroup containing a nonzero elementary root is the whole
rank-four group.  This is the strongest existing normal-generation theorem
needed after a root has been detected. -/
theorem normal_eq_top_of_nonzero_elementaryRoot_mem
    (N : Subgroup H) (hN : N.Normal)
    (i j : Fin 4) (hij : i ≠ j) (a : R) (ha : a ≠ 0)
    (hmem : elementaryRoot i j hij a ∈ N) :
    N = ⊤ := by
  letI : N.Normal := hN
  exact elementaryGroup_normal_eq_top_of_elementaryRoot_mem
    three_le_card N hij hmem (coefficient_unit_sandwich a ha)

/-- A root coefficient occurring in a proper normal subgroup must vanish. -/
theorem elementaryRoot_coefficient_eq_zero_of_mem_proper_normal
    (N : Subgroup H) (hN : N.Normal) (hproper : N ≠ ⊤)
    (i j : Fin 4) (hij : i ≠ j) (a : R)
    (hmem : elementaryRoot i j hij a ∈ N) :
    a = 0 := by
  by_contra ha
  exact hproper
    (normal_eq_top_of_nonzero_elementaryRoot_mem N hN i j hij a ha hmem)

/-- Equivalently, every proper normal subgroup has trivial intersection with
each additive elementary root subgroup. -/
theorem properNormal_inf_elementaryRootSubgroup_eq_bot
    (N : Subgroup H) (hN : N.Normal) (hproper : N ≠ ⊤)
    (i j : Fin 4) (hij : i ≠ j) :
    N ⊓ elementaryRootSubgroup i j hij = ⊥ := by
  refine le_bot_iff.mp ?_
  intro g hg
  obtain ⟨hgN, hgRoot⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨a, ha⟩ :=
    (mem_elementaryRootSubgroup_iff i j hij g).mp hgRoot
  have ha0 := elementaryRoot_coefficient_eq_zero_of_mem_proper_normal
    N hN hproper i j hij a (ha.symm ▸ hgN)
  apply Subgroup.mem_bot.mpr
  rw [← ha, ha0, elementaryRoot_zero]

/-! ## The canonical level and the scalar branch -/

/-- The exact manuscript coefficient ring has single-sandwich division. -/
theorem coefficientRing_hasSingleSandwichDivision :
    HasSingleSandwichDivision R := by
  change HasSingleSandwichDivision
    (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
  exact BinaryLeavitt.hasSingleSandwichDivision (ZMod 2)

/-- The exact manuscript coefficient ring is simple.  This is obtained from
the already proved single-sandwich division theorem, not assumed as an
instance. -/
theorem coefficientRing_isSimple : IsSimpleRing R := by
  exact HasSingleSandwichDivision.isSimpleRing
    coefficientRing_hasSingleSandwichDivision

/-- The centre of the exact rank-four elementary group is trivial. -/
theorem rankFour_center_eq_bot : Subgroup.center H = ⊥ := by
  change Subgroup.center
    (elementaryGroup (Fin 4)
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) = ⊥
  exact ElementarySimplicity.center_elementaryGroup_eq_bot_of_units
    BinaryLeavitt.central_units_trivial

/-- Every proper normal subgroup of the exact rank-four group has zero
canonical elementary level.  Thus the nonzero-level branch of the manuscript's
Preusser case split is now unconditional. -/
theorem normalLevel_eq_bot_of_proper_normal
    (N : Subgroup H) (hN : N.Normal) (hproper : N ≠ ⊤) :
    normalLevel three_le_card N = ⊥ := by
  letI : N.Normal := hN
  by_contra hlevel
  apply hproper
  exact normal_eq_top_of_normalLevel_ne_bot three_le_card
    coefficient_unit_sandwich N hlevel

/-- The final exact reduction after the canonical-level construction: it is
enough to prove that a normal subgroup with zero level is central.  The centre
calculation and the nonzero-level branch are discharged here. -/
theorem isSimpleGroup_of_levelZero_central
    (hzero : ∀ (N : Subgroup H) (hN : N.Normal),
      normalLevel (hN := hN) three_le_card N = ⊥ →
      N ≤ Subgroup.center H) :
    IsSimpleGroup H where
  exists_pair_ne := ⟨defect, 1, defect_ne_one⟩
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    by_cases htop : N = ⊤
    · exact Or.inr htop
    · left
      have hlevel := normalLevel_eq_bot_of_proper_normal N hN htop
      have hle : N ≤ ⊥ := by
        rw [← rankFour_center_eq_bot]
        exact hzero N hN hlevel
      exact le_bot_iff.mp hle

/-- No nontrivial elementary root is central in the rank-four group.  This
uses only a third index and the Steinberg commutator relation; it does not need
the unavailable computation of the full group centre. -/
theorem elementaryRoot_mem_center_iff
    (i j : Fin 4) (hij : i ≠ j) (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.center H ↔ a = 0 := by
  constructor
  · intro hcenter
    obtain ⟨k, hki, hkj⟩ := exists_third_index three_le_card i j
    have hik : i ≠ k := Ne.symm hki
    have hjk : j ≠ k := Ne.symm hkj
    have hcomm : Commute (elementaryRoot i j hij a)
        (elementaryRoot j k hjk 1) :=
      (Subgroup.mem_center_iff.mp hcenter
        (elementaryRoot j k hjk 1)).symm
    have hroot : elementaryRoot i k hik (a * 1) = 1 := by
      rw [← elementaryRoot_commutator i j k hij hjk hik]
      exact commutatorElement_eq_one_iff_commute.mpr hcomm
    simpa using (elementaryRoot_eq_one_iff i k hik (a * 1)).mp hroot
  · rintro rfl
    simp

/-- Exact reduction of Proposition `prop:simple` to root detection.  All work
after detection is discharged by
`normal_eq_top_of_nonzero_elementaryRoot_mem`. -/
theorem isSimpleGroup_of_normal_root_detection
    (hdetect : ∀ (N : Subgroup H), N.Normal → N ≠ ⊥ →
      ∃ (i j : Fin 4) (hij : i ≠ j) (a : R),
        a ≠ 0 ∧ elementaryRoot i j hij a ∈ N) :
    IsSimpleGroup H where
  exists_pair_ne := ⟨defect, 1, defect_ne_one⟩
  eq_bot_or_eq_top_of_normal := by
    intro N hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · refine Or.inr ?_
      obtain ⟨i, j, hij, a, ha, hmem⟩ := hdetect N hN hbot
      exact normal_eq_top_of_nonzero_elementaryRoot_mem
        N hN i j hij a ha hmem

/-! ## Unconditional rank-four closure -/

/-- Every nontrivial normal subgroup of the exact manuscript group contains a
nonzero elementary root. -/
theorem normalRootDetection :
    ∀ (N : Subgroup H), N.Normal → N ≠ ⊥ →
      ∃ (i j : Fin 4) (hij : i ≠ j) (a : R),
        a ≠ 0 ∧ elementaryRoot i j hij a ∈ N := by
  change ElementarySimplicity.RootDetection (Fin 4) R
  exact rootDetection_of_leavittFamily three_le_card leavittFamily
    coefficient_unit_sandwich
    BinaryLeavitt.central_units_trivial

/-- **Proposition `prop:simple`.**  The rank-four binary Leavitt elementary
group is simple, with no caller-supplied normal-structure hypothesis. -/
theorem manuscriptPropositionSimple : PropositionSimple := by
  exact isSimpleGroup_of_normal_root_detection normalRootDetection

end RankFourEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
