import GroupApproximation.CharClass.LIXSectionPath

/-!
# The manuscript's section of `W_g` has exactly one zero, in the clutched-circle model

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionPath.lean` shows the manuscript's pair — the constant `e` on the
northern half of the circle, the path (2.10) on the southern half — descends to a
genuine section of the mapping torus `W_g` built in
`CharClass/MappingTorusProjection.lean`.  This file locates that section's zero: combining
`MappingTorusSection.lean`'s zero-locus lemma with `LIXSectionPath.lean`'s
`unitVectors_seam_eq_zero_iff` and `manuscriptPath_eq_zero_iff_split`, the zero sits at
exactly the point the manuscript's Lemma 2 needs it at — the *south pole* of the circle
(height `-1`, horizontal coordinate `0`), together with `b = -a` in the trivial block and
`c = 0` in the transverse block.

This is the same linear-algebra content as `AlgTop/ManuscriptSectionZeroCount.lean`'s
`manuscriptSection_eq_zero_iff`, run in the clutched-circle model of `S¹` instead of the
raw `[0,1]` interval that file uses: no cohomology, no derivative, no orientation.

## Main results

* `blockNorth`, `blockSouth` — the manuscript's pair, in the block-split form
  `manuscriptPath_eq_zero_iff_split` consumes.
* `height_eq_neg_one_of_horiz_eq_zero` — on the open southern half, horizontal
  coordinate `0` forces height `-1`: the only such point is the south pole.
* `mtSection_manuscript_eq_zero_iff` — **the zero locus**: the transported section
  vanishes at `p` iff `p`'s circle point is the south pole, `b = -a` in the trivial
  block at `p`'s base point, and `c` vanishes there in the transverse block.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {M Z : Type*} [TopologicalSpace M] [TopologicalSpace Z]

/-! ## 1. The manuscript's pair, in block-split form -/

/-- The manuscript's northern field, block-split: the constant `a` in the trivial
block, nothing in the transverse block. -/
def blockNorth (a : M → ι → ℂ) (p : Z × M) : ι ⊕ κ → ℂ := Sum.elim (a p.2) 0

/-- The manuscript's southern field along the path (2.10), block-split: the straight
path from `a` to `b` in the trivial block, the scaled transverse section `χ • c` in the
other, reparametrised by the circle's horizontal coordinate. -/
def blockSouth (a b : M → ι → ℂ) (c : M → κ → ℂ) (χ : ℝ → ℝ) (y : Z → ℝ)
    (p : Z × M) : ι ⊕ κ → ℂ :=
  manuscriptPath (fun m => Sum.elim (a m) 0) (fun m => Sum.elim (b m) 0)
    (fun m => Sum.elim (0 : ι → ℂ) (c m)) χ (southParam y p.1) p.2

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- `Sum.elim` into the *left* slot of two independently-typed blocks is continuous.
Unlike `MappingTorusSection.lean`'s `continuous_sumElim_left` (stated for the doubled
index `n ⊕ n` that clutching produces), this is the version for the two *different*
index types `ι` (the trivial block) and `κ` (the transverse block) that the
manuscript's `V = 1³ ⊕ H` actually splits into. -/
theorem continuous_sumElim_left' {X : Type*} [TopologicalSpace X] {u : X → ι → ℂ}
    (hu : Continuous u) : Continuous fun x => Sum.elim (u x) (0 : κ → ℂ) := by
  refine continuous_pi fun z => ?_
  cases z with
  | inl i =>
    have h : Continuous fun x => u x i := (continuous_apply i).comp hu
    simpa using h
  | inr k => simpa using continuous_const

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- The mixed-type analogue of `continuous_sumElim_right`. -/
theorem continuous_sumElim_right' {X : Type*} [TopologicalSpace X] {v : X → κ → ℂ}
    (hv : Continuous v) : Continuous fun x => Sum.elim (0 : ι → ℂ) (v x) := by
  refine continuous_pi fun z => ?_
  cases z with
  | inl i => simpa using continuous_const
  | inr k =>
    have h : Continuous fun x => v x k := (continuous_apply k).comp hv
    simpa using h

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem continuous_blockNorth {a : M → ι → ℂ} (ha : Continuous a) :
    Continuous (blockNorth (κ := κ) (Z := Z) a) :=
  (continuous_sumElim_left' ha).comp continuous_snd

theorem continuous_blockSouth {a b : M → ι → ℂ} {c : M → κ → ℂ} {χ : ℝ → ℝ} {y : Z → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hχ : Continuous χ)
    (hy : Continuous y) : Continuous (blockSouth a b c χ y) :=
  continuous_manuscriptPath (continuous_sumElim_left' ha) (continuous_sumElim_left' hb)
    (continuous_sumElim_right' hc) hχ ((continuous_southParam hy).comp continuous_fst)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- `Sum.elim` of two independently-typed blocks vanishes iff both blocks do. Unlike
`MappingTorusSection.lean`'s `sumElim_eq_zero_iff` (stated for the doubled index `n ⊕ n`
that clutching produces), this is the version for the two *different* index types `ι`
(the trivial block) and `κ` (the transverse block) that the manuscript's `V = 1³ ⊕ H`
actually splits into. -/
theorem sumElim_eq_zero_iff' {u : ι → ℂ} {v : κ → ℂ} :
    Sum.elim u v = (0 : ι ⊕ κ → ℂ) ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun k => congrFun h (Sum.inr k)⟩
  · rintro ⟨hu, hv⟩
    funext x
    cases x with
    | inl i => simpa using congrFun hu i
    | inr k => simpa using congrFun hv k

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [TopologicalSpace M] [TopologicalSpace Z] in
theorem blockNorth_eq_zero_iff {a : M → ι → ℂ} (p : Z × M) :
    blockNorth (κ := κ) a p = 0 ↔ a p.2 = 0 := by
  rw [blockNorth, sumElim_eq_zero_iff']
  simp

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [TopologicalSpace M] [TopologicalSpace Z] in
theorem blockNorth_ne_zero {a : M → ι → ℂ} {p : Z × M} (ha : a p.2 ≠ 0) :
    blockNorth (κ := κ) a p ≠ 0 := fun h => ha (blockNorth_eq_zero_iff p |>.mp h)

omit [TopologicalSpace M] [TopologicalSpace Z] in
theorem blockSouth_eq_zero_iff (a b : M → ι → ℂ) (c : M → κ → ℂ) (χ : ℝ → ℝ)
    (y : Z → ℝ) (p : Z × M) :
    blockSouth a b c χ y p = 0 ↔
      ((∀ i, ((1 - southParam y p.1 : ℝ) : ℂ) * a p.2 i
          + ((southParam y p.1 : ℝ) : ℂ) * b p.2 i = 0) ∧
        ∀ k, ((χ (southParam y p.1) : ℝ) : ℂ) * c p.2 k = 0) :=
  manuscriptPath_eq_zero_iff_split χ (southParam y p.1) p.2

/-- **The manuscript's pair really is section data**, in block-split form: the seam
condition is `G` applied to the constant block `a` equalling the block `b` (the
manuscript's own `g e = s`). -/
theorem isMTSectionData_blockSplit {V G : M → Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ} {y t : Z → ℝ}
    {a b : M → ι → ℂ} {c : M → κ → ℂ} {χ : ℝ → ℝ} (hch : IsCircleChart y t)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hχ : Continuous χ)
    (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (haV : ∀ m, V m *ᵥ Sum.elim (a m) (0 : κ → ℂ) = Sum.elim (a m) 0)
    (hbV : ∀ m, V m *ᵥ Sum.elim (b m) (0 : κ → ℂ) = Sum.elim (b m) 0)
    (hcV : ∀ m, V m *ᵥ Sum.elim (0 : ι → ℂ) (c m) = Sum.elim (0 : ι → ℂ) (c m))
    (hGa : ∀ m, G m *ᵥ Sum.elim (a m) (0 : κ → ℂ) = Sum.elim (b m) 0) :
    IsMTSectionData V G y t (blockNorth a) (blockSouth a b c χ y) :=
  isMTSectionData_manuscript hch (continuous_sumElim_left' ha) (continuous_sumElim_left' hb)
    (continuous_sumElim_right' hc) hχ hχ0 hχ1 haV hbV hcV hGa

/-! ## 2. The south pole, from its coordinates -/

/-- On the open southern half of a circle chart, horizontal coordinate `0` forces
height `-1`. Together with `horiz_eq_zero_of_height_eq_one`/`_neg_one` this pins the
south pole as the unique point of the closed southern half with horizontal
coordinate `0`. -/
theorem height_eq_neg_one_of_horiz_eq_zero {y t : Z → ℝ} (hch : IsCircleChart y t) {z : Z}
    (hy : y z = 0) (ht : t z < 0) : t z = -1 := by
  have hc := hch.circle z
  rw [hy] at hc
  have hfac : (t z - 1) * (t z + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linarith : t z = 1) (by linarith)
  · linarith

/-! ## 3. The zero locus -/

/-- **The zero locus of the manuscript's section, transported into the clutched-circle
mapping torus.**  There is no zero on the closed northern half (the constant field `a`
is nonvanishing there); on the open southern half the section vanishes exactly at the
south pole (horizontal coordinate `0`, height `-1`), with `b = -a` in the trivial block
and `c = 0` in the transverse block at the base point. -/
theorem mtSection_manuscript_eq_zero_iff
    {V G : M → Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ} {y t : Z → ℝ}
    {a b : M → ι → ℂ} {c : M → κ → ℂ} {χ : ℝ → ℝ}
    (hch : IsCircleChart y t)
    (hd : IsMTSectionData V G y t (blockNorth a) (blockSouth a b c χ y))
    (ha0 : ∀ m, a m ≠ 0) (haNorm : ∀ m, ∑ i, ‖a m i‖ ^ 2 = 1)
    (hbNorm : ∀ m, ∑ i, ‖b m i‖ ^ 2 = 1) (hχhalf : χ (1 / 2 : ℝ) = 1) (p : Z × M) :
    mtSection V G y t (blockNorth a) (blockSouth a b c χ y) p = 0
      ↔ (t p.1 = -1 ∧ y p.1 = 0 ∧ b p.2 = -a p.2 ∧ c p.2 = 0) := by
  rw [mtSection_eq_zero_iff_of_north_ne_zero hd (fun q => blockNorth_ne_zero (ha0 q.2)),
    blockSouth_eq_zero_iff]
  have hτmem := southParam_mem_Icc hch p.1
  have hiff := unitVectors_seam_eq_zero_iff (haNorm p.2) (hbNorm p.2) hτmem.1 hτmem.2
  constructor
  · rintro ⟨ht0, hseam, hχ0⟩
    obtain ⟨hτ, hba⟩ := hiff.mp hseam
    have hy0 : y p.1 = 0 := southParam_eq_half_iff.mp hτ
    refine ⟨height_eq_neg_one_of_horiz_eq_zero hch hy0 ht0, hy0, funext hba, funext ?_⟩
    intro k
    have hk := hχ0 k
    rw [hτ, hχhalf] at hk
    simpa using hk
  · rintro ⟨ht0, hy0, hba, hc0⟩
    have hτ : southParam y p.1 = 1 / 2 := southParam_eq_half_iff.mpr hy0
    refine ⟨by rw [ht0]; norm_num, hiff.mpr ⟨hτ, fun i => congrFun hba i⟩, fun k => ?_⟩
    rw [hτ, hχhalf, congrFun hc0 k]
    simp

end GroupApproximation.CharClass
