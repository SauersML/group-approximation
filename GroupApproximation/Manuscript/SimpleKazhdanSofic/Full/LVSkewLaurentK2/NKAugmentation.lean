import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Augmentation of the half rings and twisted nil-`K₂` (lane LVSkewLaurentK2-3b)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Work order
WO-LVCohnK2-3, lane 3b, has to prove `HalfK2Statement S`: stable `K₂ = 0` for the half rings
`S[t;φ] = skewHalf S 1` and `S[t⁻¹;φ⁻¹] = skewHalf S (-1)` of the skew Laurent ring over an
ultramatricial `𝔽₂`-ring `S` (Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*,
Münster J. Math. 2 (2009), `thm:skewyao`, Steps 1-2, `yaoseq6.tex` l.574-640; Yao 1995,
Thm 2.1).  In degree two this splits as `K₂(S[t^ε;φ^ε]) = K₂(S) ⊕ NK₂(S,φ)_ε`, and the second
summand vanishes for regular supercoherent coefficients (`yaoseq6.tex` l.1169ff).

This file sets up the splitting at finite stages:

* `halfSupport S ε`: the subring of Laurent series with no coefficients in degrees of sign `-ε`;
* `skewHalf_le_halfSupport`: the half ring `skewHalf S ε` lies in it;
* `halfAug S ε hε : skewHalf S ε →+* S`: the augmentation `t^ε ↦ 0` (coefficient of `t⁰`);
* `halfAug_comp_halfConst`: the augmentation retracts the constants;
* `NilK2Trivial S ε hε`: vanishing of twisted nil-`K₂` at finite stages, i.e. every element of
  `K₂(n, S[t^ε;φ^ε])` in the kernel of the augmentation dies after padding;
* `baseSurjective_halfConst_of_nilK2Trivial`: `NilK2Trivial` makes `K₂(S) → K₂(S[t^ε;φ^ε])`
  stably surjective, so that `LVStableK2.stableK2Trivial_of_baseSurjective` reduces
  `HalfK2Statement S` to stable `K₂(S) = 0` and `NilK2Trivial S (±1)`;
* `halfK2Statement_of_nilK2Trivial`: that reduction.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

open SteinbergGroup

section Support

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- Products of Laurent series without coefficients in degrees of sign `-ε` have no such
coefficients.  (`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem halfSupported_mul {ε : ℤ} {x y : SkewLaurent S}
    (hx : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff x g = 0)
    (hy : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff y g = 0) :
    ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff (x * y) g = 0 := by
  intro g hg
  rw [SkewMonoidAlgebra.coeff_mul_left]
  show ∑ a ∈ SkewMonoidAlgebra.support x,
    SkewMonoidAlgebra.coeff x a * a • SkewMonoidAlgebra.coeff y (a⁻¹ * g) = 0
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : ε * Multiplicative.toAdd a < 0
  · rw [hx a ha, zero_mul]
  · have ha' : 0 ≤ ε * Multiplicative.toAdd a := not_lt.mp ha
    have hb : ε * Multiplicative.toAdd (a⁻¹ * g) < 0 := by
      rw [toAdd_mul, toAdd_inv, mul_add, mul_neg]
      linarith
    rw [hy _ hb, smul_zero, mul_zero]

/-- The unit has no coefficients in nonzero degrees.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfSupported_one (ε : ℤ) :
    ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff (1 : SkewLaurent S) g = 0 := by
  intro g hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [toAdd_one, mul_zero] at hg
    exact (lt_irrefl _) hg
  rw [SkewMonoidAlgebra.coeff_one, Finsupp.single_eq_of_ne hg1]

/-- Sums of half-supported Laurent series are half-supported.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfSupported_add {ε : ℤ} {x y : SkewLaurent S}
    (hx : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff x g = 0)
    (hy : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff y g = 0) :
    ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff (x + y) g = 0 := by
  intro g hg
  rw [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, hx g hg, hy g hg, add_zero]

/-- Negatives of half-supported Laurent series are half-supported.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfSupported_neg {ε : ℤ} {x : SkewLaurent S}
    (hx : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff x g = 0) :
    ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff (-x) g = 0 := by
  intro g hg
  rw [SkewMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hx g hg, neg_zero]

/-- Zero is half-supported.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfSupported_zero (ε : ℤ) :
    ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff (0 : SkewLaurent S) g = 0 := by
  intro g _
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- For `ε ≠ 0`, the coefficient of `t⁰` is multiplicative on half-supported Laurent series:
only the pair of degrees `(0, 0)` contributes.  (`yaoseq6.tex` `thm:skewyao`, Step 1, the
augmentation `R[t₊] → R`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem coeff_one_mul_of_halfSupported {ε : ℤ} (hε : ε ≠ 0) {x y : SkewLaurent S}
    (hx : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff x g = 0)
    (hy : ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
      SkewMonoidAlgebra.coeff y g = 0) :
    SkewMonoidAlgebra.coeff (x * y) 1 =
      SkewMonoidAlgebra.coeff x 1 * SkewMonoidAlgebra.coeff y 1 := by
  rw [SkewMonoidAlgebra.coeff_mul_left]
  show ∑ a ∈ SkewMonoidAlgebra.support x,
      SkewMonoidAlgebra.coeff x a * a • SkewMonoidAlgebra.coeff y (a⁻¹ * 1) =
    SkewMonoidAlgebra.coeff x 1 * SkewMonoidAlgebra.coeff y 1
  rw [Finset.sum_eq_single (1 : Multiplicative ℤ)]
  · rw [inv_one, mul_one (1 : Multiplicative ℤ), one_smul]
  · intro a _ ha
    by_cases hneg : ε * Multiplicative.toAdd a < 0
    · rw [hx a hneg, zero_mul]
    · have hne : ε * Multiplicative.toAdd a ≠ 0 :=
        mul_ne_zero hε fun h0 => ha (toAdd_eq_zero.mp h0)
      have hpos : 0 < ε * Multiplicative.toAdd a := lt_of_le_of_ne (not_lt.mp hneg) hne.symm
      have hb : ε * Multiplicative.toAdd (a⁻¹ * 1) < 0 := by
        rw [mul_one a⁻¹, toAdd_inv, mul_neg]
        linarith
      rw [hy _ hb, smul_zero, mul_zero]
  · intro h1
    rw [SkewMonoidAlgebra.notMem_support_iff.mp h1, zero_mul]

end Support

section Augmentation

variable (S : Type*) [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- The subring of Laurent series `Σ s_m t^m` with `s_m = 0` whenever `ε m < 0`; for `ε = 1`
these are the series in nonnegative degrees.  (`yaoseq6.tex` `thm:skewyao`, Step 1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def halfSupport (ε : ℤ) : Subring (SkewLaurent S) where
  carrier := {x | ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
    SkewMonoidAlgebra.coeff x g = 0}
  mul_mem' hx hy := halfSupported_mul (S := S) (ε := ε) hx hy
  one_mem' := halfSupported_one (S := S) ε
  add_mem' hx hy := halfSupported_add (S := S) (ε := ε) hx hy
  zero_mem' := halfSupported_zero (S := S) ε
  neg_mem' hx := halfSupported_neg (S := S) (ε := ε) hx

/-- Membership in `halfSupport S ε`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem mem_halfSupport {ε : ℤ} {x : SkewLaurent S} :
    x ∈ halfSupport S ε ↔
      ∀ g : Multiplicative ℤ, ε * Multiplicative.toAdd g < 0 →
        SkewMonoidAlgebra.coeff x g = 0 :=
  Iff.rfl

/-- The half ring `S[t^ε;φ^ε]` consists of half-supported Laurent series: its generators, the
constants and `t^ε`, are half-supported.  (`yaoseq6.tex` `thm:skewyao`, Step 1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skewHalf_le_halfSupport (ε : ℤ) : skewHalf S ε ≤ halfSupport S ε := by
  refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
  · rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, mem_halfSupport]
    intro g hg
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [toAdd_one, mul_zero] at hg
      exact (lt_irrefl _) hg
    change SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) g = 0
    rw [SkewMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hg1]
  · rintro _ rfl
    rw [SetLike.mem_coe, mem_halfSupport]
    intro g hg
    have hg1 : g ≠ Multiplicative.ofAdd ε := by
      rintro rfl
      rw [toAdd_ofAdd] at hg
      exact absurd hg (not_lt.mpr (mul_self_nonneg ε))
    change SkewMonoidAlgebra.coeff
      (SkewMonoidAlgebra.single (Multiplicative.ofAdd ε) (1 : S)) g = 0
    rw [SkewMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hg1]

/-- For `ε ≠ 0`, the coefficient of `t⁰` is a ring map on `halfSupport S ε`.
(`yaoseq6.tex` `thm:skewyao`, Step 1, the augmentation `R[t₊] → R`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def halfSupportAug (ε : ℤ) (hε : ε ≠ 0) : halfSupport S ε →+* S where
  toFun x := SkewMonoidAlgebra.coeff (x : SkewLaurent S) 1
  map_one' := by
    change SkewMonoidAlgebra.coeff (1 : SkewLaurent S) 1 = 1
    rw [SkewMonoidAlgebra.coeff_one, Finsupp.single_eq_same]
  map_mul' x y := by
    change SkewMonoidAlgebra.coeff ((x : SkewLaurent S) * (y : SkewLaurent S)) 1 =
      SkewMonoidAlgebra.coeff (x : SkewLaurent S) 1 * SkewMonoidAlgebra.coeff (y : SkewLaurent S) 1
    exact coeff_one_mul_of_halfSupported hε ((mem_halfSupport S).mp x.2)
      ((mem_halfSupport S).mp y.2)
  map_zero' := by
    change SkewMonoidAlgebra.coeff (0 : SkewLaurent S) 1 = 0
    rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  map_add' x y := by
    change SkewMonoidAlgebra.coeff ((x : SkewLaurent S) + (y : SkewLaurent S)) 1 =
      SkewMonoidAlgebra.coeff (x : SkewLaurent S) 1 + SkewMonoidAlgebra.coeff (y : SkewLaurent S) 1
    rw [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply]

/-- The augmentation `S[t^ε;φ^ε] → S`, `t^ε ↦ 0`, for `ε ≠ 0`.
(`yaoseq6.tex` `thm:skewyao`, Step 1, the augmentation `R[t₊] → R`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def halfAug (ε : ℤ) (hε : ε ≠ 0) : skewHalf S ε →+* S :=
  (halfSupportAug S ε hε).comp (Subring.inclusion (skewHalf_le_halfSupport S ε))

/-- The augmentation takes the coefficient of `t⁰`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfAug_apply (ε : ℤ) (hε : ε ≠ 0) (x : skewHalf S ε) :
    halfAug S ε hε x = SkewMonoidAlgebra.coeff (x : SkewLaurent S) 1 :=
  rfl

/-- The augmentation retracts the constants, elementwise.
(`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfAug_halfConst (ε : ℤ) (hε : ε ≠ 0) (a : S) : halfAug S ε hε (halfConst S ε a) = a := by
  rw [halfAug_apply]
  change SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) 1 = a
  rw [SkewMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- The augmentation retracts the constants.
(`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfAug_comp_halfConst (ε : ℤ) (hε : ε ≠ 0) :
    (halfAug S ε hε).comp (halfConst S ε) = RingHom.id S :=
  RingHom.ext fun a => halfAug_halfConst S ε hε a

/-- **Twisted nil-`K₂` vanishes at finite stages**: every element of `K₂(n, S[t^ε;φ^ε])` in the
kernel of the augmentation `S[t^ε;φ^ε] → S` dies after padding.  This is `NK₂(S, φ)_ε = 0`
(`yaoseq6.tex` l.1169ff: `NK(R,φ)_± = 0` for regular supercoherent `R`; Yao 1995, Thm 2.1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def NilK2Trivial (ε : ℤ) (hε : ε ≠ 0) : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) (skewHalf S ε)), projection k = 1 →
    ringMap (halfAug S ε hε) k = 1 → ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) k = 1

/-- **Splitting `K₂(S[t^ε;φ^ε]) = K₂(S) ⊕ NK₂(S,φ)_ε`, surjectivity half.**  If twisted nil-`K₂`
vanishes, then every element `k` of `K₂(n, S[t^ε;φ^ε])` is, after padding, the image of an
element of `K₂(N, S)`: namely of the augmentation of `k`, since `k · (const (aug k))⁻¹` lies in
both kernels.  (`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem baseSurjective_halfConst_of_nilK2Trivial (ε : ℤ) (hε : ε ≠ 0)
    (hN : NilK2Trivial S ε hε) : LVStableK2.StableK2BaseSurjective (halfConst S ε) := by
  intro n k hk
  have hy : projection (ringMap (halfAug S ε hε) k) = 1 := by
    rw [LVCohnK2.projection_ringMap, hk, map_one]
  have hk' : projection (k * (ringMap (halfConst S ε) (ringMap (halfAug S ε hε) k))⁻¹) = 1 := by
    rw [map_mul, map_inv, LVCohnK2.projection_ringMap, hy, map_one, hk, inv_one, mul_one]
  have hk'' :
      ringMap (halfAug S ε hε) (k * (ringMap (halfConst S ε) (ringMap (halfAug S ε hε) k))⁻¹) =
        1 := by
    rw [map_mul, map_inv, LVCohnK2.ringMap_ringMap, halfAug_comp_halfConst,
      LVCohnK2.ringMap_id_apply, mul_inv_cancel]
  obtain ⟨N, hnN, hNk⟩ := hN n _ hk' hk''
  refine ⟨N, hnN, indexMap (Fin.castLEEmb hnN) (ringMap (halfAug S ε hε) k),
    LVH2GL3.projection_indexMap_eq_one (Fin.castLEEmb hnN) hy, ?_⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at hNk
  rw [← LVStableK2.indexMap_ringMap]
  exact hNk.symm

/-- **Reduction of lane 3b.**  Stable `K₂(S) = 0` together with `NK₂(S,φ)_± = 0` gives
`HalfK2Statement S`.  (`yaoseq6.tex` `thm:skewyao`, Steps 1-2, l.574-640, and l.1169ff;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfK2Statement_of_nilK2Trivial (hK2 : LVH2GL3.StableK2Trivial S)
    (hpos : NilK2Trivial S 1 one_ne_zero) (hneg : NilK2Trivial S (-1) (by decide)) :
    HalfK2Statement S := by
  show LVH2GL3.StableK2Trivial (skewHalf S 1) ∧ LVH2GL3.StableK2Trivial (skewHalf S (-1))
  exact ⟨LVStableK2.stableK2Trivial_of_baseSurjective (halfConst S 1)
      (baseSurjective_halfConst_of_nilK2Trivial S 1 one_ne_zero hpos) hK2,
    LVStableK2.stableK2Trivial_of_baseSurjective (halfConst S (-1))
      (baseSurjective_halfConst_of_nilK2Trivial S (-1) _ hneg) hK2⟩

end Augmentation

end GroupApproximation.Full.LVSkewLaurentK2
