import GroupApproximation.PropertyT.KassabovBorelMeasureInequalities
import GroupApproximation.PropertyT.KassabovTorusNumerics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Exact geometry for the rank-zero torus argument

This file develops the exact geometry in Kassabov's two-dimensional torus
argument.  The four elementary shears are honest Borel automorphisms of
`(R / Z)^2`.  Their images of arbitrary coordinate rectangles are computed
exactly.  We choose the centered fundamental-domain representative in
`(-1/2, 1/2]`, define the two outer strips and the punctured central square,
and cut the shear transports of its same-sign and opposite-sign halves into
four central sectors and four overflow sectors.

The set-theoretic transports to the two sign halves are proved below.  Each
sign half is identified with the union of its two central cuts, and the two
vertical and two horizontal overflow containments are proved directly.  These
facts give the four diagrammatic identities:

* `g12+ '' (A 3 ∪ A' 4) = A 3 ∪ A 4`;
* `g21+ '' (A' 3 ∪ A 4) = A 3 ∪ A 4`;
* `g12- '' (A' 1 ∪ A 2) = A 1 ∪ A 2`;
* `g21- '' (A 1 ∪ A' 2) = A 1 ∪ A 2`.

Every set identity and containment used in this geometric step is proved in
this file; none is introduced as a predicate or assumption.
-/

namespace GroupApproximation

namespace KassabovRankZeroTorusGeometry

open MeasureTheory Set

/-- The two-dimensional unit additive torus. -/
abbrev Torus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The positive upper elementary shear `(x, y) ↦ (x + y, y)`. -/
def g12Plus : Equiv.Perm Torus where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv := by
    rintro ⟨x, y⟩
    simp
  right_inv := by
    rintro ⟨x, y⟩
    simp

/-- The negative upper elementary shear `(x, y) ↦ (x - y, y)`. -/
def g12Minus : Equiv.Perm Torus := g12Plus.symm

/-- The positive lower elementary shear `(x, y) ↦ (x, x + y)`. -/
def g21Plus : Equiv.Perm Torus where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv := by
    rintro ⟨x, y⟩
    simp
  right_inv := by
    rintro ⟨x, y⟩
    simp

/-- The negative lower elementary shear `(x, y) ↦ (x, y - x)`. -/
def g21Minus : Equiv.Perm Torus := g21Plus.symm

@[simp] theorem g12Plus_apply (p : Torus) :
    g12Plus p = (p.1 + p.2, p.2) := rfl

@[simp] theorem g12Minus_apply (p : Torus) :
    g12Minus p = (p.1 - p.2, p.2) := rfl

@[simp] theorem g21Plus_apply (p : Torus) :
    g21Plus p = (p.1, p.1 + p.2) := rfl

@[simp] theorem g21Minus_apply (p : Torus) :
    g21Minus p = (p.1, p.2 - p.1) := rfl

@[simp] theorem g12Plus_symm : g12Plus.symm = g12Minus := rfl

@[simp] theorem g12Minus_symm : g12Minus.symm = g12Plus := rfl

@[simp] theorem g21Plus_symm : g21Plus.symm = g21Minus := rfl

@[simp] theorem g21Minus_symm : g21Minus.symm = g21Plus := rfl

theorem measurable_g12Plus : Measurable (g12Plus : Torus → Torus) :=
  (measurable_fst.add measurable_snd).prodMk measurable_snd

theorem measurable_g12Minus : Measurable (g12Minus : Torus → Torus) :=
  (measurable_fst.sub measurable_snd).prodMk measurable_snd

theorem measurable_g21Plus : Measurable (g21Plus : Torus → Torus) :=
  measurable_fst.prodMk (measurable_fst.add measurable_snd)

theorem measurable_g21Minus : Measurable (g21Minus : Torus → Torus) :=
  measurable_fst.prodMk (measurable_snd.sub measurable_fst)

/-- The positive upper shear, including measurability of its inverse. -/
def measurableEquivG12Plus : Torus ≃ᵐ Torus where
  toEquiv := g12Plus
  measurable_toFun := measurable_g12Plus
  measurable_invFun := measurable_g12Minus

/-- The negative upper shear, including measurability of its inverse. -/
def measurableEquivG12Minus : Torus ≃ᵐ Torus := measurableEquivG12Plus.symm

/-- The positive lower shear, including measurability of its inverse. -/
def measurableEquivG21Plus : Torus ≃ᵐ Torus where
  toEquiv := g21Plus
  measurable_toFun := measurable_g21Plus
  measurable_invFun := measurable_g21Minus

/-- The negative lower shear, including measurability of its inverse. -/
def measurableEquivG21Minus : Torus ≃ᵐ Torus := measurableEquivG21Plus.symm

private theorem image_equiv_eq_preimage_symm {X : Type*}
    (e : Equiv.Perm X) (s : Set X) :
    e '' s = e.symm ⁻¹' s := by
  ext x
  simp

/-- Exact transport of a coordinate rectangle by the positive upper shear. -/
theorem g12Plus_image_prod (s t : Set (AddCircle (1 : ℝ))) :
    g12Plus '' (s ×ˢ t) =
      {p : Torus | p.1 - p.2 ∈ s ∧ p.2 ∈ t} := by
  rw [image_equiv_eq_preimage_symm]
  rfl

/-- Exact transport of a coordinate rectangle by the negative upper shear. -/
theorem g12Minus_image_prod (s t : Set (AddCircle (1 : ℝ))) :
    g12Minus '' (s ×ˢ t) =
      {p : Torus | p.1 + p.2 ∈ s ∧ p.2 ∈ t} := by
  rw [image_equiv_eq_preimage_symm]
  rfl

/-- Exact transport of a coordinate rectangle by the positive lower shear. -/
theorem g21Plus_image_prod (s t : Set (AddCircle (1 : ℝ))) :
    g21Plus '' (s ×ˢ t) =
      {p : Torus | p.1 ∈ s ∧ p.2 - p.1 ∈ t} := by
  rw [image_equiv_eq_preimage_symm]
  rfl

/-- Exact transport of a coordinate rectangle by the negative lower shear. -/
theorem g21Minus_image_prod (s t : Set (AddCircle (1 : ℝ))) :
    g21Minus '' (s ×ˢ t) =
      {p : Torus | p.1 ∈ s ∧ p.1 + p.2 ∈ t} := by
  rw [image_equiv_eq_preimage_symm]
  rfl

/-- The representative of a circle point in the centered interval
`(-1/2, 1/2]`. -/
noncomputable def centeredRepresentative (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x : ℝ)

theorem measurable_centeredRepresentative : Measurable centeredRepresentative :=
  measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ))).measurable

@[simp] theorem coe_centeredRepresentative (x : AddCircle (1 : ℝ)) :
    ((centeredRepresentative x : ℝ) : AddCircle (1 : ℝ)) = x := by
  exact AddCircle.coe_equivIoc
    (p := (1 : ℝ)) (a := -(1 / 2 : ℝ)) (y := x)

theorem centeredRepresentative_coe_eq {x : ℝ}
    (hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) :
    centeredRepresentative (x : AddCircle (1 : ℝ)) = x := by
  have h := AddCircle.equivIoc_coe_eq
    (p := (1 : ℝ)) (a := -(1 / 2 : ℝ)) hx
  exact congrArg Subtype.val h

theorem centeredRepresentative_add_eq (x y : AddCircle (1 : ℝ))
    (hxy : centeredRepresentative x + centeredRepresentative y ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) :
    centeredRepresentative (x + y) =
      centeredRepresentative x + centeredRepresentative y := by
  have hcoe :
      ((centeredRepresentative x + centeredRepresentative y : ℝ) :
        AddCircle (1 : ℝ)) = x + y := by
    rw [AddCircle.coe_add, coe_centeredRepresentative,
      coe_centeredRepresentative]
  rw [← hcoe]
  exact centeredRepresentative_coe_eq hxy

theorem centeredRepresentative_sub_eq (x y : AddCircle (1 : ℝ))
    (hxy : centeredRepresentative x - centeredRepresentative y ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) :
    centeredRepresentative (x - y) =
      centeredRepresentative x - centeredRepresentative y := by
  have hcoe :
      ((centeredRepresentative x - centeredRepresentative y : ℝ) :
        AddCircle (1 : ℝ)) = x - y := by
    rw [AddCircle.coe_sub, coe_centeredRepresentative,
      coe_centeredRepresentative]
  rw [← hcoe]
  exact centeredRepresentative_coe_eq hxy

/-- Points whose first centered coordinate lies outside the open central
interval `(-1/4, 1/4)`. -/
def verticalOuter : Set Torus :=
  {p | (1 / 4 : ℝ) ≤ |centeredRepresentative p.1|}

/-- Points whose second centered coordinate lies outside the open central
interval `(-1/4, 1/4)`. -/
def horizontalOuter : Set Torus :=
  {p | (1 / 4 : ℝ) ≤ |centeredRepresentative p.2|}

/-- The open central coordinate square. -/
def centralSquare : Set Torus :=
  {p | |centeredRepresentative p.1| < (1 / 4 : ℝ) ∧
    |centeredRepresentative p.2| < (1 / 4 : ℝ)}

/-- The central square with the trivial character removed. -/
def puncturedCentralSquare : Set Torus := centralSquare \ {(0, 0)}

theorem measurableSet_verticalOuter : MeasurableSet verticalOuter := by
  exact measurableSet_le measurable_const
    ((measurable_centeredRepresentative.comp measurable_fst).abs)

theorem measurableSet_horizontalOuter : MeasurableSet horizontalOuter := by
  exact measurableSet_le measurable_const
    ((measurable_centeredRepresentative.comp measurable_snd).abs)

theorem measurableSet_centralSquare : MeasurableSet centralSquare := by
  exact (measurableSet_lt
    ((measurable_centeredRepresentative.comp measurable_fst).abs)
    measurable_const).inter
    (measurableSet_lt
      ((measurable_centeredRepresentative.comp measurable_snd).abs)
      measurable_const)

theorem measurableSet_puncturedCentralSquare :
    MeasurableSet puncturedCentralSquare :=
  measurableSet_centralSquare.diff (measurableSet_singleton (0, 0))

/-! ### The eight shear sectors -/

/-- The same-sign half of the punctured central square. -/
def sameSignCentral : Set Torus :=
  puncturedCentralSquare ∩
    {p | 0 < centeredRepresentative p.1 * centeredRepresentative p.2 ∨
      centeredRepresentative p.2 = 0}

/-- The complementary sign half.  The boundary convention assigns the
horizontal axis to `sameSignCentral` and the vertical axis to this half; this
is exactly what makes both diagonal shear transports exhaustive. -/
def oppositeSignCentral : Set Torus :=
  puncturedCentralSquare \ sameSignCentral

theorem measurableSet_sameSignCentral : MeasurableSet sameSignCentral := by
  exact measurableSet_puncturedCentralSquare.inter
    ((measurableSet_lt measurable_const
        ((measurable_centeredRepresentative.comp measurable_fst).mul
          (measurable_centeredRepresentative.comp measurable_snd))).union
      (measurableSet_eq_fun
        (measurable_centeredRepresentative.comp measurable_snd)
        measurable_const))

theorem measurableSet_oppositeSignCentral :
    MeasurableSet oppositeSignCentral := by
  exact measurableSet_puncturedCentralSquare.diff measurableSet_sameSignCentral

theorem sameSignCentral_union_oppositeSignCentral :
    sameSignCentral ∪ oppositeSignCentral = puncturedCentralSquare := by
  rw [oppositeSignCentral, union_sdiff_self]
  exact union_eq_right.mpr inter_subset_left

theorem disjoint_sameSignCentral_oppositeSignCentral :
    Disjoint sameSignCentral oppositeSignCentral :=
  disjoint_sdiff_right

@[simp] theorem centeredRepresentative_zero :
    centeredRepresentative (0 : AddCircle (1 : ℝ)) = 0 := by
  apply centeredRepresentative_coe_eq
  norm_num

theorem centeredRepresentative_eq_zero_iff (x : AddCircle (1 : ℝ)) :
    centeredRepresentative x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hcoe := coe_centeredRepresentative x
    rw [hx] at hcoe
    exact hcoe.symm
  · rintro rfl
    exact centeredRepresentative_zero

theorem mem_oppositeSignCentral_iff (p : Torus) :
    p ∈ oppositeSignCentral ↔
      p ∈ puncturedCentralSquare ∧
        (centeredRepresentative p.1 * centeredRepresentative p.2 < 0 ∨
          centeredRepresentative p.1 = 0) := by
  constructor
  · rintro ⟨hp, hnotSame⟩
    refine ⟨hp, ?_⟩
    have hnotCond : ¬
        (0 < centeredRepresentative p.1 * centeredRepresentative p.2 ∨
          centeredRepresentative p.2 = 0) := by
      intro hcond
      exact hnotSame ⟨hp, hcond⟩
    by_cases hneg :
        centeredRepresentative p.1 * centeredRepresentative p.2 < 0
    · exact Or.inl hneg
    · right
      have hzero : centeredRepresentative p.1 *
          centeredRepresentative p.2 = 0 := by
        apply le_antisymm (le_of_not_gt (fun h ↦ hnotCond (Or.inl h)))
        exact not_lt.mp hneg
      exact (mul_eq_zero.mp hzero).resolve_right
        (fun hy ↦ hnotCond (Or.inr hy))
  · rintro ⟨hp, hsign⟩
    refine ⟨hp, ?_⟩
    rintro ⟨_, hsame⟩
    rcases hsign with hneg | hx
    · rcases hsame with hpos | hy
      · exact (not_lt_of_ge hpos.le) hneg
      · rw [hy, mul_zero] at hneg
        exact (lt_irrefl 0) hneg
    · rcases hsame with hpos | hy
      · rw [hx, zero_mul] at hpos
        exact (lt_irrefl 0) hpos
      · apply hp.2
        have hp1 : p.1 = 0 := (centeredRepresentative_eq_zero_iff p.1).mp hx
        have hp2 : p.2 = 0 := (centeredRepresentative_eq_zero_iff p.2).mp hy
        exact Set.mem_singleton_iff.mpr (Prod.ext hp1 hp2)

private theorem sameSign_real_shear_dichotomy {x y : ℝ}
    (hx : |x| < (1 / 4 : ℝ)) (hy : |y| < (1 / 4 : ℝ))
    (hsign : 0 < x * y ∨ y = 0) :
    (|y - x| < (1 / 4 : ℝ) ∧
        (0 < x * (y - x) ∨ y - x = 0)) ∨
      (|x - y| < (1 / 4 : ℝ) ∧
        (0 < (x - y) * y ∨ y = 0)) := by
  rcases hsign with hprod | rfl
  · rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · by_cases hxy : x ≤ y
      · left
        constructor
        · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
          have hy' := (abs_lt.mp hy).2
          linarith
        · by_cases heq : x = y
          · exact Or.inr (sub_eq_zero.mpr heq.symm)
          · exact Or.inl (mul_pos hpos.1 (sub_pos.mpr (lt_of_le_of_ne hxy heq)))
      · right
        have hyx : y < x := lt_of_not_ge hxy
        constructor
        · rw [abs_of_nonneg (sub_nonneg.mpr hyx.le)]
          have hx' := (abs_lt.mp hx).2
          linarith
        · exact Or.inl (mul_pos (sub_pos.mpr hyx) hpos.2)
    · by_cases hyx : y ≤ x
      · left
        constructor
        · rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
          have hy' := (abs_lt.mp hy).1
          linarith
        · by_cases heq : y = x
          · exact Or.inr (sub_eq_zero.mpr heq)
          · exact Or.inl
              (mul_pos_of_neg_of_neg hneg.1
                (sub_neg.mpr (lt_of_le_of_ne hyx heq)))
      · right
        have hxy : x < y := lt_of_not_ge hyx
        constructor
        · rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)]
          have hx' := (abs_lt.mp hx).1
          linarith
        · exact Or.inl
            (mul_pos_of_neg_of_neg (sub_neg.mpr hxy) hneg.2)
  · right
    simpa using hx

private theorem oppositeSign_real_shear_dichotomy {x y : ℝ}
    (hx : |x| < (1 / 4 : ℝ)) (hy : |y| < (1 / 4 : ℝ))
    (hsign : x * y < 0 ∨ x = 0) :
    (|x + y| < (1 / 4 : ℝ) ∧
        ((x + y) * y < 0 ∨ x + y = 0)) ∨
      (|x + y| < (1 / 4 : ℝ) ∧
        (x * (x + y) < 0 ∨ x = 0)) := by
  rcases hsign with hprod | rfl
  · rcases (mul_neg_iff.mp hprod) with hposneg | hnegpos
    · by_cases hsum : 0 ≤ x + y
      · left
        constructor
        · rw [abs_of_nonneg hsum]
          have hx' := (abs_lt.mp hx).2
          linarith
        · by_cases heq : x + y = 0
          · exact Or.inr heq
          · exact Or.inl
              (mul_neg_of_pos_of_neg (lt_of_le_of_ne hsum (Ne.symm heq))
                hposneg.2)
      · right
        have hsumNeg : x + y < 0 := lt_of_not_ge hsum
        constructor
        · rw [abs_of_neg hsumNeg]
          have hy' := (abs_lt.mp hy).1
          linarith
        · exact Or.inl (mul_neg_of_pos_of_neg hposneg.1 hsumNeg)
    · by_cases hsum : x + y ≤ 0
      · left
        constructor
        · rw [abs_of_nonpos hsum]
          have hx' := (abs_lt.mp hx).1
          linarith
        · by_cases heq : x + y = 0
          · exact Or.inr heq
          · exact Or.inl
              (mul_neg_of_neg_of_pos (lt_of_le_of_ne hsum heq) hnegpos.2)
      · right
        have hsumPos : 0 < x + y := lt_of_not_ge hsum
        constructor
        · rw [abs_of_pos hsumPos]
          have hy' := (abs_lt.mp hy).2
          linarith
        · exact Or.inl (mul_neg_of_neg_of_pos hnegpos.1 hsumPos)
  · right
    constructor
    · simpa using hy
    · exact Or.inr rfl

private theorem sameSign_real_shear_exclusive {x y : ℝ}
    (hne : x ≠ 0 ∨ y ≠ 0)
    (h1 : 0 < x * (y - x) ∨ y - x = 0)
    (h2 : 0 < (x - y) * y ∨ y = 0) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · nlinarith [sq_nonneg (x - y)]
  · rw [h2, zero_sub, mul_neg] at h1
    nlinarith [sq_nonneg x]
  · rw [sub_eq_zero.mp h1, sub_self, zero_mul] at h2
    exact (lt_irrefl 0) h2
  · apply hne.elim
    · intro hx
      apply hx
      rw [h2] at h1
      linarith
    · intro hy
      exact hy h2

private theorem oppositeSign_real_shear_exclusive {x y : ℝ}
    (hne : x ≠ 0 ∨ y ≠ 0)
    (h3 : (x + y) * y < 0 ∨ x + y = 0)
    (h4 : x * (x + y) < 0 ∨ x = 0) : False := by
  rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
  · nlinarith [sq_nonneg (x + y)]
  · rw [h4, zero_add] at h3
    exact (not_lt_of_ge (mul_self_nonneg y)) h3
  · rw [h3, mul_zero] at h4
    exact (lt_irrefl 0) h4
  · apply hne.elim
    · exact fun hx ↦ hx h4
    · intro hy
      apply hy
      rw [h4, zero_add] at h3
      exact h3

/-- The part of a transported sign half that remains in the central square. -/
def centralCut (s : Set Torus) : Set Torus := s ∩ centralSquare

/-- The part of a transported sign half that leaves the central square. -/
def outerCut (s : Set Torus) : Set Torus := s \ centralSquare

theorem centralCut_union_outerCut (s : Set Torus) :
    centralCut s ∪ outerCut s = s := by
  ext p
  simp [centralCut, outerCut]

theorem outerCut_union_centralCut (s : Set Torus) :
    outerCut s ∪ centralCut s = s := by
  rw [union_comm, centralCut_union_outerCut]

theorem disjoint_centralCut_outerCut (s t : Set Torus) :
    Disjoint (centralCut s) (outerCut t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact hq.2 hp.2

theorem disjoint_outerCut_centralCut (s t : Set Torus) :
    Disjoint (outerCut s) (centralCut t) :=
  (disjoint_centralCut_outerCut t s).symm

theorem measurableSet_centralCut {s : Set Torus} (hs : MeasurableSet s) :
    MeasurableSet (centralCut s) :=
  hs.inter measurableSet_centralSquare

theorem measurableSet_outerCut {s : Set Torus} (hs : MeasurableSet s) :
    MeasurableSet (outerCut s) :=
  hs.diff measurableSet_centralSquare

/-- Same-sign, vertically dominant central sector. -/
def sector1 : Set Torus :=
  centralCut (g21Plus '' sameSignCentral)

/-- Same-sign, horizontally dominant central sector. -/
def sector2 : Set Torus :=
  centralCut (g12Plus '' sameSignCentral)

/-- Opposite-sign, horizontally dominant central sector. -/
def sector3 : Set Torus :=
  centralCut (g12Minus '' oppositeSignCentral)

/-- Opposite-sign, vertically dominant central sector. -/
def sector4 : Set Torus :=
  centralCut (g21Minus '' oppositeSignCentral)

/-- The vertical overflow paired with `sector1`. -/
def sectorPrime1 : Set Torus :=
  outerCut (g12Plus '' sameSignCentral)

/-- The horizontal overflow paired with `sector2`. -/
def sectorPrime2 : Set Torus :=
  outerCut (g21Plus '' sameSignCentral)

/-- The horizontal overflow paired with `sector3`. -/
def sectorPrime3 : Set Torus :=
  outerCut (g21Minus '' oppositeSignCentral)

/-- The vertical overflow paired with `sector4`. -/
def sectorPrime4 : Set Torus :=
  outerCut (g12Minus '' oppositeSignCentral)

theorem measurableSet_sector1 : MeasurableSet sector1 :=
  measurableSet_centralCut
    (measurableEquivG21Plus.measurableSet_image.mpr
      measurableSet_sameSignCentral)

theorem measurableSet_sector2 : MeasurableSet sector2 :=
  measurableSet_centralCut
    (measurableEquivG12Plus.measurableSet_image.mpr
      measurableSet_sameSignCentral)

theorem measurableSet_sector3 : MeasurableSet sector3 :=
  measurableSet_centralCut
    (measurableEquivG12Minus.measurableSet_image.mpr
      measurableSet_oppositeSignCentral)

theorem measurableSet_sector4 : MeasurableSet sector4 :=
  measurableSet_centralCut
    (measurableEquivG21Minus.measurableSet_image.mpr
      measurableSet_oppositeSignCentral)

theorem measurableSet_sectorPrime1 : MeasurableSet sectorPrime1 :=
  measurableSet_outerCut
    (measurableEquivG12Plus.measurableSet_image.mpr
      measurableSet_sameSignCentral)

theorem measurableSet_sectorPrime2 : MeasurableSet sectorPrime2 :=
  measurableSet_outerCut
    (measurableEquivG21Plus.measurableSet_image.mpr
      measurableSet_sameSignCentral)

theorem measurableSet_sectorPrime3 : MeasurableSet sectorPrime3 :=
  measurableSet_outerCut
    (measurableEquivG21Minus.measurableSet_image.mpr
      measurableSet_oppositeSignCentral)

theorem measurableSet_sectorPrime4 : MeasurableSet sectorPrime4 :=
  measurableSet_outerCut
    (measurableEquivG12Minus.measurableSet_image.mpr
      measurableSet_oppositeSignCentral)

theorem disjoint_sector3_sectorPrime4 : Disjoint sector3 sectorPrime4 :=
  disjoint_centralCut_outerCut _ _

theorem disjoint_sectorPrime3_sector4 : Disjoint sectorPrime3 sector4 :=
  disjoint_outerCut_centralCut _ _

theorem disjoint_sectorPrime1_sector2 : Disjoint sectorPrime1 sector2 :=
  disjoint_outerCut_centralCut _ _

theorem disjoint_sector1_sectorPrime2 : Disjoint sector1 sectorPrime2 :=
  disjoint_centralCut_outerCut _ _

theorem sameSignCentral_subset_sector1_union_sector2 :
    sameSignCentral ⊆ sector1 ∪ sector2 := by
  intro p hp
  rcases sameSign_real_shear_dichotomy hp.1.1.1 hp.1.1.2 hp.2 with h1 | h2
  · have hIoc : centeredRepresentative p.2 - centeredRepresentative p.1 ∈
        Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      have hb := abs_lt.mp h1.1
      constructor <;> norm_num <;> linarith
    have hrep := centeredRepresentative_sub_eq p.2 p.1 hIoc
    have hq : g21Minus p ∈ sameSignCentral := by
      constructor
      · constructor
        · constructor
          · exact hp.1.1.1
          · change |centeredRepresentative (p.2 - p.1)| < (1 / 4 : ℝ)
            rw [hrep]
            exact h1.1
        · intro hzero
          have hqzero : g21Minus p = (0, 0) := by simpa using hzero
          apply hp.1.2
          have hpzero : p = (0, 0) := by
            calc
              p = g21Plus (g21Minus p) := by simp
              _ = g21Plus (0, 0) := congrArg g21Plus hqzero
              _ = (0, 0) := by simp
          exact Set.mem_singleton_iff.mpr hpzero
      · change 0 < centeredRepresentative p.1 *
            centeredRepresentative (p.2 - p.1) ∨
          centeredRepresentative (p.2 - p.1) = 0
        rw [hrep]
        exact h1.2
    exact Or.inl ⟨⟨g21Minus p, hq, by simp⟩, hp.1.1⟩
  · have hIoc : centeredRepresentative p.1 - centeredRepresentative p.2 ∈
        Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      have hb := abs_lt.mp h2.1
      constructor <;> norm_num <;> linarith
    have hrep := centeredRepresentative_sub_eq p.1 p.2 hIoc
    have hq : g12Minus p ∈ sameSignCentral := by
      constructor
      · constructor
        · constructor
          · change |centeredRepresentative (p.1 - p.2)| < (1 / 4 : ℝ)
            rw [hrep]
            exact h2.1
          · exact hp.1.1.2
        · intro hzero
          have hqzero : g12Minus p = (0, 0) := by simpa using hzero
          apply hp.1.2
          have hpzero : p = (0, 0) := by
            calc
              p = g12Plus (g12Minus p) := by simp
              _ = g12Plus (0, 0) := congrArg g12Plus hqzero
              _ = (0, 0) := by simp
          exact Set.mem_singleton_iff.mpr hpzero
      · change 0 < centeredRepresentative (p.1 - p.2) *
            centeredRepresentative p.2 ∨ centeredRepresentative p.2 = 0
        rw [hrep]
        exact h2.2
    exact Or.inr ⟨⟨g12Minus p, hq, by simp⟩, hp.1.1⟩

theorem oppositeSignCentral_subset_sector3_union_sector4 :
    oppositeSignCentral ⊆ sector3 ∪ sector4 := by
  intro p hp
  have hp' := (mem_oppositeSignCentral_iff p).mp hp
  rcases oppositeSign_real_shear_dichotomy hp'.1.1.1 hp'.1.1.2 hp'.2 with h3 | h4
  · have hIoc : centeredRepresentative p.1 + centeredRepresentative p.2 ∈
        Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      have hb := abs_lt.mp h3.1
      constructor <;> norm_num <;> linarith
    have hrep := centeredRepresentative_add_eq p.1 p.2 hIoc
    have hq : g12Plus p ∈ oppositeSignCentral := by
      rw [mem_oppositeSignCentral_iff]
      constructor
      · constructor
        · constructor
          · change |centeredRepresentative (p.1 + p.2)| < (1 / 4 : ℝ)
            rw [hrep]
            exact h3.1
          · exact hp'.1.1.2
        · intro hzero
          have hqzero : g12Plus p = (0, 0) := by simpa using hzero
          apply hp'.1.2
          have hpzero : p = (0, 0) := by
            calc
              p = g12Minus (g12Plus p) := by simp
              _ = g12Minus (0, 0) := congrArg g12Minus hqzero
              _ = (0, 0) := by simp
          exact Set.mem_singleton_iff.mpr hpzero
      · change centeredRepresentative (p.1 + p.2) *
            centeredRepresentative p.2 < 0 ∨
          centeredRepresentative (p.1 + p.2) = 0
        rw [hrep]
        exact h3.2
    exact Or.inl ⟨⟨g12Plus p, hq, by simp⟩, hp'.1.1⟩
  · have hIoc : centeredRepresentative p.1 + centeredRepresentative p.2 ∈
        Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      have hb := abs_lt.mp h4.1
      constructor <;> norm_num <;> linarith
    have hrep := centeredRepresentative_add_eq p.1 p.2 hIoc
    have hq : g21Plus p ∈ oppositeSignCentral := by
      rw [mem_oppositeSignCentral_iff]
      constructor
      · constructor
        · constructor
          · exact hp'.1.1.1
          · change |centeredRepresentative (p.1 + p.2)| < (1 / 4 : ℝ)
            rw [hrep]
            exact h4.1
        · intro hzero
          have hqzero : g21Plus p = (0, 0) := by simpa using hzero
          apply hp'.1.2
          have hpzero : p = (0, 0) := by
            calc
              p = g21Minus (g21Plus p) := by simp
              _ = g21Minus (0, 0) := congrArg g21Minus hqzero
              _ = (0, 0) := by simp
          exact Set.mem_singleton_iff.mpr hpzero
      · change centeredRepresentative p.1 *
            centeredRepresentative (p.1 + p.2) < 0 ∨
          centeredRepresentative p.1 = 0
        rw [hrep]
        exact h4.2
    exact Or.inr ⟨⟨g21Plus p, hq, by simp⟩, hp'.1.1⟩

theorem sector1_subset_sameSignCentral : sector1 ⊆ sameSignCentral := by
  rintro _ ⟨⟨q, hq, rfl⟩, hcentral⟩
  have hIoc : centeredRepresentative q.1 + centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq.1.1.1
    have hy := abs_lt.mp hq.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq q.1 q.2 hIoc
  constructor
  · constructor
    · exact hcentral
    · intro hzero
      have hout : g21Plus q = (0, 0) := by simpa using hzero
      have hqzero : q = (0, 0) := g21Plus.injective (by simpa using hout)
      exact hq.1.2 (Set.mem_singleton_iff.mpr hqzero)
  · change 0 < centeredRepresentative q.1 *
        centeredRepresentative (q.1 + q.2) ∨
      centeredRepresentative (q.1 + q.2) = 0
    rcases hq.2 with hprod | hyzero
    · left
      rw [hrep]
      rcases mul_pos_iff.mp hprod with hpos | hneg
      · exact mul_pos hpos.1 (by linarith)
      · exact mul_pos_of_neg_of_neg hneg.1 (by linarith)
    · left
      have hxne : centeredRepresentative q.1 ≠ 0 := by
        intro hxzero
        apply hq.1.2
        have hq1 : q.1 = 0 := (centeredRepresentative_eq_zero_iff q.1).mp hxzero
        have hq2 : q.2 = 0 := (centeredRepresentative_eq_zero_iff q.2).mp hyzero
        exact Set.mem_singleton_iff.mpr (Prod.ext hq1 hq2)
      rw [hrep, hyzero, add_zero]
      exact mul_self_pos.mpr hxne

theorem sector2_subset_sameSignCentral : sector2 ⊆ sameSignCentral := by
  rintro _ ⟨⟨q, hq, rfl⟩, hcentral⟩
  have hIoc : centeredRepresentative q.1 + centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq.1.1.1
    have hy := abs_lt.mp hq.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq q.1 q.2 hIoc
  constructor
  · constructor
    · exact hcentral
    · intro hzero
      have hout : g12Plus q = (0, 0) := by simpa using hzero
      have hqzero : q = (0, 0) := g12Plus.injective (by simpa using hout)
      exact hq.1.2 (Set.mem_singleton_iff.mpr hqzero)
  · change 0 < centeredRepresentative (q.1 + q.2) *
        centeredRepresentative q.2 ∨ centeredRepresentative q.2 = 0
    rcases hq.2 with hprod | hyzero
    · left
      rw [hrep]
      rcases mul_pos_iff.mp hprod with hpos | hneg
      · exact mul_pos (by linarith) hpos.2
      · exact mul_pos_of_neg_of_neg (by linarith) hneg.2
    · exact Or.inr hyzero

theorem sector1_union_sector2 :
    sector1 ∪ sector2 = sameSignCentral := by
  apply Subset.antisymm
  · exact union_subset sector1_subset_sameSignCentral
      sector2_subset_sameSignCentral
  · exact sameSignCentral_subset_sector1_union_sector2

theorem sector3_subset_oppositeSignCentral :
    sector3 ⊆ oppositeSignCentral := by
  rintro _ ⟨⟨q, hq, rfl⟩, hcentral⟩
  have hq' := (mem_oppositeSignCentral_iff q).mp hq
  have hIoc : centeredRepresentative q.1 - centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq'.1.1.1
    have hy := abs_lt.mp hq'.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq q.1 q.2 hIoc
  rw [mem_oppositeSignCentral_iff]
  constructor
  · constructor
    · exact hcentral
    · intro hzero
      have hout : g12Minus q = (0, 0) := by simpa using hzero
      have hqzero : q = (0, 0) := g12Minus.injective (by simpa using hout)
      exact hq'.1.2 (Set.mem_singleton_iff.mpr hqzero)
  · change centeredRepresentative (q.1 - q.2) *
        centeredRepresentative q.2 < 0 ∨
      centeredRepresentative (q.1 - q.2) = 0
    left
    rw [hrep]
    rcases hq'.2 with hprod | hxzero
    · rcases mul_neg_iff.mp hprod with hposneg | hnegpos
      · exact mul_neg_of_pos_of_neg (by linarith) hposneg.2
      · exact mul_neg_of_neg_of_pos (by linarith) hnegpos.2
    · have hyne : centeredRepresentative q.2 ≠ 0 := by
        intro hyzero
        apply hq'.1.2
        have hq1 : q.1 = 0 := (centeredRepresentative_eq_zero_iff q.1).mp hxzero
        have hq2 : q.2 = 0 := (centeredRepresentative_eq_zero_iff q.2).mp hyzero
        exact Set.mem_singleton_iff.mpr (Prod.ext hq1 hq2)
      rw [hxzero, zero_sub, neg_mul]
      exact neg_lt_zero.mpr (mul_self_pos.mpr hyne)

theorem sector4_subset_oppositeSignCentral :
    sector4 ⊆ oppositeSignCentral := by
  rintro _ ⟨⟨q, hq, rfl⟩, hcentral⟩
  have hq' := (mem_oppositeSignCentral_iff q).mp hq
  have hIoc : centeredRepresentative q.2 - centeredRepresentative q.1 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq'.1.1.1
    have hy := abs_lt.mp hq'.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq q.2 q.1 hIoc
  rw [mem_oppositeSignCentral_iff]
  constructor
  · constructor
    · exact hcentral
    · intro hzero
      have hout : g21Minus q = (0, 0) := by simpa using hzero
      have hqzero : q = (0, 0) := g21Minus.injective (by simpa using hout)
      exact hq'.1.2 (Set.mem_singleton_iff.mpr hqzero)
  · change centeredRepresentative q.1 *
        centeredRepresentative (q.2 - q.1) < 0 ∨
      centeredRepresentative q.1 = 0
    rcases hq'.2 with hprod | hxzero
    · left
      rw [hrep]
      rcases mul_neg_iff.mp hprod with hposneg | hnegpos
      · exact mul_neg_of_pos_of_neg hposneg.1 (by linarith)
      · exact mul_neg_of_neg_of_pos hnegpos.1 (by linarith)
    · exact Or.inr hxzero

theorem sector3_union_sector4 :
    sector3 ∪ sector4 = oppositeSignCentral := by
  apply Subset.antisymm
  · exact union_subset sector3_subset_oppositeSignCentral
      sector4_subset_oppositeSignCentral
  · exact oppositeSignCentral_subset_sector3_union_sector4

private theorem centered_pair_ne_zero_of_mem_puncturedCentralSquare
    {p : Torus} (hp : p ∈ puncturedCentralSquare) :
    centeredRepresentative p.1 ≠ 0 ∨ centeredRepresentative p.2 ≠ 0 := by
  by_cases hx : centeredRepresentative p.1 = 0
  · right
    intro hy
    apply hp.2
    have hp1 : p.1 = 0 := (centeredRepresentative_eq_zero_iff p.1).mp hx
    have hp2 : p.2 = 0 := (centeredRepresentative_eq_zero_iff p.2).mp hy
    exact Set.mem_singleton_iff.mpr (Prod.ext hp1 hp2)
  · exact Or.inl hx

private theorem mem_sector1_sign_condition {p : Torus} (hp : p ∈ sector1) :
    0 < centeredRepresentative p.1 *
        (centeredRepresentative p.2 - centeredRepresentative p.1) ∨
      centeredRepresentative p.2 - centeredRepresentative p.1 = 0 := by
  rcases hp with ⟨⟨q, hq, hqp⟩, hpCentral⟩
  have hqeq : q = g21Minus p := by
    apply g21Plus.injective
    rw [hqp]
    simp
  rw [hqeq] at hq
  have hsign := hq.2
  have hIoc : centeredRepresentative p.2 - centeredRepresentative p.1 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hpCentral.1
    have hy := abs_lt.mp hpCentral.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq p.2 p.1 hIoc
  change 0 < centeredRepresentative p.1 *
        centeredRepresentative (p.2 - p.1) ∨
      centeredRepresentative (p.2 - p.1) = 0 at hsign
  rwa [hrep] at hsign

private theorem mem_sector2_sign_condition {p : Torus} (hp : p ∈ sector2) :
    0 < (centeredRepresentative p.1 - centeredRepresentative p.2) *
        centeredRepresentative p.2 ∨ centeredRepresentative p.2 = 0 := by
  rcases hp with ⟨⟨q, hq, hqp⟩, hpCentral⟩
  have hqeq : q = g12Minus p := by
    apply g12Plus.injective
    rw [hqp]
    simp
  rw [hqeq] at hq
  have hsign := hq.2
  have hIoc : centeredRepresentative p.1 - centeredRepresentative p.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hpCentral.1
    have hy := abs_lt.mp hpCentral.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq p.1 p.2 hIoc
  change 0 < centeredRepresentative (p.1 - p.2) *
        centeredRepresentative p.2 ∨ centeredRepresentative p.2 = 0 at hsign
  rwa [hrep] at hsign

theorem disjoint_sector1_sector2 : Disjoint sector1 sector2 := by
  rw [Set.disjoint_left]
  intro p h1 h2
  exact sameSign_real_shear_exclusive
    (centered_pair_ne_zero_of_mem_puncturedCentralSquare
      (sector1_subset_sameSignCentral h1).1)
    (mem_sector1_sign_condition h1) (mem_sector2_sign_condition h2)

private theorem mem_sector3_sign_condition {p : Torus} (hp : p ∈ sector3) :
    (centeredRepresentative p.1 + centeredRepresentative p.2) *
        centeredRepresentative p.2 < 0 ∨
      centeredRepresentative p.1 + centeredRepresentative p.2 = 0 := by
  rcases hp with ⟨⟨q, hq, hqp⟩, hpCentral⟩
  have hqeq : q = g12Plus p := by
    apply g12Minus.injective
    rw [hqp]
    simp
  rw [hqeq] at hq
  have hq' := (mem_oppositeSignCentral_iff _).mp hq
  have hsign := hq'.2
  have hIoc : centeredRepresentative p.1 + centeredRepresentative p.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hpCentral.1
    have hy := abs_lt.mp hpCentral.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq p.1 p.2 hIoc
  change centeredRepresentative (p.1 + p.2) *
        centeredRepresentative p.2 < 0 ∨
      centeredRepresentative (p.1 + p.2) = 0 at hsign
  rwa [hrep] at hsign

private theorem mem_sector4_sign_condition {p : Torus} (hp : p ∈ sector4) :
    centeredRepresentative p.1 *
        (centeredRepresentative p.1 + centeredRepresentative p.2) < 0 ∨
      centeredRepresentative p.1 = 0 := by
  rcases hp with ⟨⟨q, hq, hqp⟩, hpCentral⟩
  have hqeq : q = g21Plus p := by
    apply g21Minus.injective
    rw [hqp]
    simp
  rw [hqeq] at hq
  have hq' := (mem_oppositeSignCentral_iff _).mp hq
  have hsign := hq'.2
  have hIoc : centeredRepresentative p.1 + centeredRepresentative p.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hpCentral.1
    have hy := abs_lt.mp hpCentral.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq p.1 p.2 hIoc
  change centeredRepresentative p.1 *
        centeredRepresentative (p.1 + p.2) < 0 ∨
      centeredRepresentative p.1 = 0 at hsign
  rwa [hrep] at hsign

theorem disjoint_sector3_sector4 : Disjoint sector3 sector4 := by
  rw [Set.disjoint_left]
  intro p h3 h4
  exact oppositeSign_real_shear_exclusive
    (centered_pair_ne_zero_of_mem_puncturedCentralSquare
      ((mem_oppositeSignCentral_iff p).mp
        (sector3_subset_oppositeSignCentral h3)).1)
    (mem_sector3_sign_condition h3) (mem_sector4_sign_condition h4)

/-! The following four identities are the exact set-theoretic transport
equalities before identifying each sign half with the union of its two
central triangular cuts. -/

theorem g12Plus_image_sector3_union_sectorPrime4 :
    g12Plus '' (sector3 ∪ sectorPrime4) = oppositeSignCentral := by
  rw [image_union]
  change g12Plus ''
      (centralCut (g12Minus '' oppositeSignCentral)) ∪
    g12Plus '' (outerCut (g12Minus '' oppositeSignCentral)) = _
  rw [← image_union, centralCut_union_outerCut]
  ext p
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hinverse : g12Plus (g12Minus r) = r := by simp
    rw [hinverse]
    exact hr
  · intro hp
    exact ⟨g12Minus p, ⟨p, hp, rfl⟩, by simp⟩

theorem g21Plus_image_sectorPrime3_union_sector4 :
    g21Plus '' (sectorPrime3 ∪ sector4) = oppositeSignCentral := by
  rw [image_union]
  change g21Plus ''
      (outerCut (g21Minus '' oppositeSignCentral)) ∪
    g21Plus '' (centralCut (g21Minus '' oppositeSignCentral)) = _
  rw [← image_union, outerCut_union_centralCut]
  ext p
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hinverse : g21Plus (g21Minus r) = r := by simp
    rw [hinverse]
    exact hr
  · intro hp
    exact ⟨g21Minus p, ⟨p, hp, rfl⟩, by simp⟩

theorem g12Minus_image_sectorPrime1_union_sector2 :
    g12Minus '' (sectorPrime1 ∪ sector2) = sameSignCentral := by
  rw [image_union]
  change g12Minus ''
      (outerCut (g12Plus '' sameSignCentral)) ∪
    g12Minus '' (centralCut (g12Plus '' sameSignCentral)) = _
  rw [← image_union, outerCut_union_centralCut]
  ext p
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hinverse : g12Minus (g12Plus r) = r := by simp
    rw [hinverse]
    exact hr
  · intro hp
    exact ⟨g12Plus p, ⟨p, hp, rfl⟩, by simp⟩

theorem g21Minus_image_sector1_union_sectorPrime2 :
    g21Minus '' (sector1 ∪ sectorPrime2) = sameSignCentral := by
  rw [image_union]
  change g21Minus ''
      (centralCut (g21Plus '' sameSignCentral)) ∪
    g21Minus '' (outerCut (g21Plus '' sameSignCentral)) = _
  rw [← image_union, centralCut_union_outerCut]
  ext p
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hinverse : g21Minus (g21Plus r) = r := by simp
    rw [hinverse]
    exact hr
  · intro hp
    exact ⟨g21Plus p, ⟨p, hp, rfl⟩, by simp⟩

/-- First exact diagrammatic transport. -/
theorem g12Plus_image_sector3_union_sectorPrime4_eq_sector3_union_sector4 :
    g12Plus '' (sector3 ∪ sectorPrime4) = sector3 ∪ sector4 := by
  calc
    g12Plus '' (sector3 ∪ sectorPrime4) = oppositeSignCentral :=
      g12Plus_image_sector3_union_sectorPrime4
    _ = sector3 ∪ sector4 := sector3_union_sector4.symm

/-- Second exact diagrammatic transport. -/
theorem g21Plus_image_sectorPrime3_union_sector4_eq_sector3_union_sector4 :
    g21Plus '' (sectorPrime3 ∪ sector4) = sector3 ∪ sector4 := by
  calc
    g21Plus '' (sectorPrime3 ∪ sector4) = oppositeSignCentral :=
      g21Plus_image_sectorPrime3_union_sector4
    _ = sector3 ∪ sector4 := sector3_union_sector4.symm

/-- Third exact diagrammatic transport. -/
theorem g12Minus_image_sectorPrime1_union_sector2_eq_sector1_union_sector2 :
    g12Minus '' (sectorPrime1 ∪ sector2) = sector1 ∪ sector2 := by
  calc
    g12Minus '' (sectorPrime1 ∪ sector2) = sameSignCentral :=
      g12Minus_image_sectorPrime1_union_sector2
    _ = sector1 ∪ sector2 := sector1_union_sector2.symm

/-- Fourth exact diagrammatic transport. -/
theorem g21Minus_image_sector1_union_sectorPrime2_eq_sector1_union_sector2 :
    g21Minus '' (sector1 ∪ sectorPrime2) = sector1 ∪ sector2 := by
  calc
    g21Minus '' (sector1 ∪ sectorPrime2) = sameSignCentral :=
      g21Minus_image_sector1_union_sectorPrime2
    _ = sector1 ∪ sector2 := sector1_union_sector2.symm

theorem fourCentralSectors_union :
    sector1 ∪ sector2 ∪ (sector3 ∪ sector4) =
      puncturedCentralSquare := by
  rw [sector1_union_sector2, sector3_union_sector4,
    sameSignCentral_union_oppositeSignCentral]

theorem sectorPrime1_subset_verticalOuter :
    sectorPrime1 ⊆ verticalOuter := by
  rintro p ⟨⟨q, hq, rfl⟩, hout⟩
  have hqCentral : q ∈ centralSquare := hq.1.1
  change (1 / 4 : ℝ) ≤
    |centeredRepresentative (g12Plus q).1|
  apply le_of_not_gt
  intro hx
  apply hout
  exact ⟨hx, by simpa using hqCentral.2⟩

theorem sectorPrime4_subset_verticalOuter :
    sectorPrime4 ⊆ verticalOuter := by
  rintro p ⟨⟨q, hq, rfl⟩, hout⟩
  have hqCentral : q ∈ centralSquare := hq.1.1
  change (1 / 4 : ℝ) ≤
    |centeredRepresentative (g12Minus q).1|
  apply le_of_not_gt
  intro hx
  apply hout
  exact ⟨hx, by simpa using hqCentral.2⟩

theorem sectorPrime2_subset_horizontalOuter :
    sectorPrime2 ⊆ horizontalOuter := by
  rintro p ⟨⟨q, hq, rfl⟩, hout⟩
  have hqCentral : q ∈ centralSquare := hq.1.1
  change (1 / 4 : ℝ) ≤
    |centeredRepresentative (g21Plus q).2|
  apply le_of_not_gt
  intro hy
  apply hout
  exact ⟨by simpa using hqCentral.1, hy⟩

theorem sectorPrime3_subset_horizontalOuter :
    sectorPrime3 ⊆ horizontalOuter := by
  rintro p ⟨⟨q, hq, rfl⟩, hout⟩
  have hqCentral : q ∈ centralSquare := hq.1.1
  change (1 / 4 : ℝ) ≤
    |centeredRepresentative (g21Minus q).2|
  apply le_of_not_gt
  intro hy
  apply hout
  exact ⟨by simpa using hqCentral.1, hy⟩

private theorem sectorPrime1_product_pos {p : Torus}
    (hp : p ∈ sectorPrime1) :
    0 < centeredRepresentative p.1 * centeredRepresentative p.2 := by
  rcases hp with ⟨⟨q, hq, rfl⟩, hout⟩
  have hIoc : centeredRepresentative q.1 + centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq.1.1.1
    have hy := abs_lt.mp hq.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq q.1 q.2 hIoc
  change 0 < centeredRepresentative (q.1 + q.2) *
    centeredRepresentative q.2
  rw [hrep]
  have hyne : centeredRepresentative q.2 ≠ 0 := by
    intro hy
    apply hout
    constructor
    · change |centeredRepresentative (q.1 + q.2)| < (1 / 4 : ℝ)
      rw [hrep, hy, add_zero]
      exact hq.1.1.1
    · exact hq.1.1.2
  rcases hq.2 with hprod | hy
  · nlinarith [sq_pos_of_ne_zero hyne]
  · exact (hyne hy).elim

private theorem sectorPrime4_product_neg {p : Torus}
    (hp : p ∈ sectorPrime4) :
    centeredRepresentative p.1 * centeredRepresentative p.2 < 0 := by
  rcases hp with ⟨⟨q, hq, rfl⟩, hout⟩
  have hq' := (mem_oppositeSignCentral_iff q).mp hq
  have hIoc : centeredRepresentative q.1 - centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq'.1.1.1
    have hy := abs_lt.mp hq'.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq q.1 q.2 hIoc
  change centeredRepresentative (q.1 - q.2) *
    centeredRepresentative q.2 < 0
  rw [hrep]
  have hyne : centeredRepresentative q.2 ≠ 0 := by
    intro hy
    apply hout
    constructor
    · change |centeredRepresentative (q.1 - q.2)| < (1 / 4 : ℝ)
      rw [hrep, hy, sub_zero]
      exact hq'.1.1.1
    · exact hq'.1.1.2
  rcases hq'.2 with hprod | hx
  · nlinarith [sq_pos_of_ne_zero hyne]
  · rw [hx, zero_sub, neg_mul]
    exact neg_lt_zero.mpr (mul_self_pos.mpr hyne)

private theorem sectorPrime2_product_pos {p : Torus}
    (hp : p ∈ sectorPrime2) :
    0 < centeredRepresentative p.1 * centeredRepresentative p.2 := by
  rcases hp with ⟨⟨q, hq, rfl⟩, hout⟩
  have hIoc : centeredRepresentative q.1 + centeredRepresentative q.2 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq.1.1.1
    have hy := abs_lt.mp hq.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_add_eq q.1 q.2 hIoc
  change 0 < centeredRepresentative q.1 *
    centeredRepresentative (q.1 + q.2)
  rw [hrep]
  have hxne : centeredRepresentative q.1 ≠ 0 := by
    intro hx
    apply hout
    constructor
    · exact hq.1.1.1
    · change |centeredRepresentative (q.1 + q.2)| < (1 / 4 : ℝ)
      rw [hrep, hx, zero_add]
      exact hq.1.1.2
  rcases hq.2 with hprod | hy
  · nlinarith [sq_pos_of_ne_zero hxne]
  · rw [hy, add_zero]
    simpa only [pow_two] using sq_pos_of_ne_zero hxne

private theorem sectorPrime3_product_neg {p : Torus}
    (hp : p ∈ sectorPrime3) :
    centeredRepresentative p.1 * centeredRepresentative p.2 < 0 := by
  rcases hp with ⟨⟨q, hq, rfl⟩, hout⟩
  have hq' := (mem_oppositeSignCentral_iff q).mp hq
  have hIoc : centeredRepresentative q.2 - centeredRepresentative q.1 ∈
      Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    have hx := abs_lt.mp hq'.1.1.1
    have hy := abs_lt.mp hq'.1.1.2
    constructor <;> norm_num <;> linarith
  have hrep := centeredRepresentative_sub_eq q.2 q.1 hIoc
  change centeredRepresentative q.1 *
    centeredRepresentative (q.2 - q.1) < 0
  rw [hrep]
  have hxne : centeredRepresentative q.1 ≠ 0 := by
    intro hx
    apply hout
    constructor
    · exact hq'.1.1.1
    · change |centeredRepresentative (q.2 - q.1)| < (1 / 4 : ℝ)
      rw [hrep, hx, sub_zero]
      exact hq'.1.1.2
  rcases hq'.2 with hprod | hx
  · nlinarith [sq_pos_of_ne_zero hxne]
  · exact (hxne hx).elim

theorem disjoint_sectorPrime1_sectorPrime4 :
    Disjoint sectorPrime1 sectorPrime4 := by
  rw [Set.disjoint_left]
  intro p h1 h4
  linarith [sectorPrime1_product_pos h1, sectorPrime4_product_neg h4]

theorem disjoint_sectorPrime2_sectorPrime3 :
    Disjoint sectorPrime2 sectorPrime3 := by
  rw [Set.disjoint_left]
  intro p h2 h3
  linarith [sectorPrime2_product_pos h2, sectorPrime3_product_neg h3]

theorem sectorPrime1_union_sectorPrime4_subset_verticalOuter :
    sectorPrime1 ∪ sectorPrime4 ⊆ verticalOuter :=
  union_subset sectorPrime1_subset_verticalOuter
    sectorPrime4_subset_verticalOuter

theorem sectorPrime2_union_sectorPrime3_subset_horizontalOuter :
    sectorPrime2 ∪ sectorPrime3 ⊆ horizontalOuter :=
  union_subset sectorPrime2_subset_horizontalOuter
    sectorPrime3_subset_horizontalOuter

/-- Every nontrivial character lies either in the punctured central square or
in one of the two outer strips. -/
theorem punctured_torus_subset :
    (Set.univ \ {(0, 0)} : Set Torus) ⊆
      puncturedCentralSquare ∪ verticalOuter ∪ horizontalOuter := by
  intro p hp
  by_cases hx : (1 / 4 : ℝ) ≤ |centeredRepresentative p.1|
  · exact Or.inl (Or.inr hx)
  by_cases hy : (1 / 4 : ℝ) ≤ |centeredRepresentative p.2|
  · exact Or.inr hy
  · exact Or.inl (Or.inl ⟨⟨lt_of_not_ge hx, lt_of_not_ge hy⟩, hp.2⟩)

/-- The measure-theoretic terminal cover inequality, with no disjointness
claim and hence no boundary-convention dependency. -/
theorem punctured_torus_mass_le
    (mu : Measure Torus) [IsFiniteMeasure mu] :
    mu.real (Set.univ \ {(0, 0)}) ≤
      mu.real puncturedCentralSquare +
        mu.real verticalOuter + mu.real horizontalOuter := by
  calc
    mu.real (Set.univ \ {(0, 0)}) ≤
        mu.real (puncturedCentralSquare ∪ verticalOuter ∪ horizontalOuter) :=
      measureReal_mono punctured_torus_subset
    _ ≤ mu.real (puncturedCentralSquare ∪ verticalOuter) +
        mu.real horizontalOuter := measureReal_union_le _ _
    _ ≤ mu.real puncturedCentralSquare +
        mu.real verticalOuter + mu.real horizontalOuter := by
      gcongr
      exact measureReal_union_le _ _

/-- Once the four exact triangular transports have supplied the quadratic
core estimate, the exact rank-zero constant follows from the genuine torus
cover and `KassabovTorusNumerics.total_mass_le`. -/
theorem total_mass_le_of_core_quadratic
    (mu : Measure Torus) [IsFiniteMeasure mu] {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hvertical : mu.real verticalOuter ≤ epsilon ^ 2 / 2)
    (hhorizontal : mu.real horizontalOuter ≤ epsilon ^ 2 / 2)
    (hquadratic :
      mu.real puncturedCentralSquare ≤ 5 * epsilon ^ 2 +
        4 * epsilon *
          Real.sqrt (mu.real puncturedCentralSquare + epsilon ^ 2)) :
    mu.real (Set.univ \ {(0, 0)}) ≤
      (2 + Real.sqrt 10) ^ 2 * epsilon ^ 2 := by
  apply KassabovTorusNumerics.total_mass_le
    (core := mu.real puncturedCentralSquare)
    (boundary := mu.real verticalOuter + mu.real horizontalOuter)
  · exact measureReal_nonneg
  · exact hepsilon
  · linarith
  · simpa only [add_assoc] using punctured_torus_mass_le mu
  · exact hquadratic

end KassabovRankZeroTorusGeometry

end GroupApproximation
