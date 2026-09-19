import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Order

/-!
# Positive extension of functionals from unital star subalgebras

The Krein extension step: a linear functional on a unital star subalgebra
of a unital C-star algebra that is nonnegative on the positives of the
ambient algebra extends to a positive linear functional on the whole
algebra.

The proof runs the M. Riesz extension theorem on the real vector space of
self-adjoint elements, against the cone of positives, with density of the
domain supplied by `IsSelfAdjoint.le_algebraMap_norm_self`; the complex
functional is then reassembled from its real and imaginary parts.  The
subalgebra is not required to be closed.

This is the extension brick of the strict-Kazhdan-compression program of
`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: it turns a character at
a spectral point of the averaging element (living on the commutative
elemental subalgebra) into a state of the full algebra, ready for GNS.
-/

namespace GroupApproximation
namespace StateExtension

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A]

private theorem star_real_smul (r : ℝ) (a : A) : star (r • a) = r • star a := by
  rw [← algebraMap_smul ℂ r a, star_smul, ← algebraMap_smul ℂ r (star a)]
  congr 1
  simp

instance : StarModule ℝ A := ⟨star_real_smul⟩

section PositiveCone

variable [PartialOrder A] [StarOrderedRing A]

/-- Nonnegative real scalars preserve positivity, directly from the
star-ordered-ring sum-of-squares description. -/
theorem real_smul_nonneg {c : ℝ} (hc : 0 ≤ c) {a : A} (ha : 0 ≤ a) :
    0 ≤ c • a := by
  rw [StarOrderedRing.nonneg_iff] at ha ⊢
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      apply AddSubmonoid.subset_closure
      refine ⟨Real.sqrt c • s, ?_⟩
      show star (Real.sqrt c • s) * (Real.sqrt c • s) = c • (star s * s)
      rw [star_smul, star_trivial, smul_mul_smul_comm,
        Real.mul_self_sqrt hc]
  | zero => rw [smul_zero]; exact AddSubmonoid.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [smul_add]; exact AddSubmonoid.add_mem _ ihx ihy

/-- The scalar `r • 1` is positive for `0 ≤ r`. -/
theorem algebraMap_real_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ algebraMap ℝ A r := by
  rw [Algebra.algebraMap_eq_smul_one, StarOrderedRing.nonneg_iff]
  apply AddSubmonoid.subset_closure
  refine ⟨Real.sqrt r • 1, ?_⟩
  show star (Real.sqrt r • 1) * (Real.sqrt r • 1) = r • (1 : A)
  rw [star_smul, star_trivial, star_one, smul_mul_smul_comm,
    Real.mul_self_sqrt hr, one_mul]

/-- The cone of positive self-adjoint elements. -/
def positiveCone : PointedCone ℝ (selfAdjoint A) where
  carrier := {a | 0 ≤ (a : A)}
  add_mem' := fun {a b} ha hb => by
    show 0 ≤ ((a + b : selfAdjoint A) : A)
    show 0 ≤ (a : A) + (b : A)
    exact add_nonneg ha hb
  zero_mem' := by
    show 0 ≤ ((0 : selfAdjoint A) : A)
    show (0 : A) ≤ 0
    exact le_refl 0
  smul_mem' := fun c {a} ha => by
    show 0 ≤ ((c • a : selfAdjoint A) : A)
    show 0 ≤ (c : ℝ) • (a : A)
    exact real_smul_nonneg c.property ha

theorem mem_positiveCone {a : selfAdjoint A} :
    a ∈ (positiveCone : PointedCone ℝ (selfAdjoint A)) ↔ 0 ≤ (a : A) :=
  Iff.rfl

end PositiveCone

section Subalgebra

variable [PartialOrder A] [StarOrderedRing A]
variable (B : StarSubalgebra ℂ A)

/-- The self-adjoint elements of the subalgebra, as the domain of the
real-linear extension problem. -/
def selfAdjointDomain : Submodule ℝ (selfAdjoint A) where
  carrier := {a | (a : A) ∈ B}
  add_mem' := fun {a b} ha hb => by
    show ((a + b : selfAdjoint A) : A) ∈ B
    show (a : A) + (b : A) ∈ B
    exact add_mem ha hb
  zero_mem' := by
    show ((0 : selfAdjoint A) : A) ∈ B
    show (0 : A) ∈ B
    exact zero_mem B
  smul_mem' := fun c a ha => by
    show ((c • a : selfAdjoint A) : A) ∈ B
    show (c : ℝ) • (a : A) ∈ B
    rw [← algebraMap_smul ℂ c (a : A)]
    exact B.smul_mem ha _

omit [PartialOrder A] [StarOrderedRing A] in
theorem mem_selfAdjointDomain {a : selfAdjoint A} :
    a ∈ selfAdjointDomain B ↔ (a : A) ∈ B :=
  Iff.rfl

variable (φ : B →ₗ[ℂ] ℂ)

/-- On self-adjoint elements of the subalgebra a positive functional takes
real values: shift by a scalar to reduce to the positive case. -/
theorem phi_real_of_isSelfAdjoint
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r)
    {b : B} (hb : IsSelfAdjoint (b : A)) :
    φ b = ((φ b).re : ℂ) := by
  set r : ℝ := ‖(b : A)‖ with hrdef
  have hu : (algebraMap ℝ A r) ∈ B := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ A]
    exact B.algebraMap_mem _
  set u : B := ⟨algebraMap ℝ A r, hu⟩ with hudef
  have hcoe : ((b + u : B) : A) = (b : A) + algebraMap ℝ A r := rfl
  have hshift : 0 ≤ ((b + u : B) : A) := by
    rw [hcoe]
    have h1 : -(b : A) ≤ algebraMap ℝ A r := by
      have h := hb.neg.le_algebraMap_norm_self
      rwa [norm_neg] at h
    have h2 := add_le_add_right h1 (b : A)
    rw [add_neg_cancel] at h2
    exact h2
  have hupos : 0 ≤ ((u : B) : A) := algebraMap_real_nonneg (norm_nonneg _)
  obtain ⟨r₁, _, hr₁⟩ := hφ (b + u) hshift
  obtain ⟨r₂, _, hr₂⟩ := hφ u hupos
  have hb' : φ b = (r₁ : ℂ) - (r₂ : ℂ) := by
    rw [← hr₁, ← hr₂, ← map_sub, add_sub_cancel_right]
  rw [hb']
  norm_num

/-- The real-linear partial functional: real part of `φ` on the
self-adjoint part of the subalgebra. -/
def realPartialFunctional : (selfAdjoint A) →ₗ.[ℝ] ℝ where
  domain := selfAdjointDomain B
  toFun :=
    { toFun := fun a => (φ ⟨((a : selfAdjoint A) : A), a.property⟩).re
      map_add' := fun a b => by
        have h : (⟨(((a + b : selfAdjointDomain B) : selfAdjoint A) : A),
            (a + b).property⟩ : B)
            = ⟨((a : selfAdjoint A) : A), a.property⟩
              + ⟨((b : selfAdjoint A) : A), b.property⟩ := by
          apply Subtype.ext
          rfl
        rw [h, map_add, Complex.add_re]
      map_smul' := fun c a => by
        have h : (⟨(((c • a : selfAdjointDomain B) : selfAdjoint A) : A),
            (c • a).property⟩ : B)
            = (c : ℂ) • ⟨((a : selfAdjoint A) : A), a.property⟩ := by
          apply Subtype.ext
          show c • ((a : selfAdjoint A) : A)
              = (c : ℂ) • ((a : selfAdjoint A) : A)
          rw [← algebraMap_smul ℂ c ((a : selfAdjoint A) : A)]
          congr 1
        rw [h, map_smul]
        simp [smul_eq_mul, Complex.mul_re]
      }

/-- The M. Riesz extension: a real-linear functional on all self-adjoint
elements, nonnegative on positives, agreeing with `Re φ` on the
subalgebra. -/
theorem exists_real_extension
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ g : (selfAdjoint A) →ₗ[ℝ] ℝ,
      (∀ x : (realPartialFunctional B φ).domain,
        g x = (realPartialFunctional B φ) x) ∧
      ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x := by
  obtain ⟨g, hg1, hg2⟩ := riesz_extension positiveCone
    (realPartialFunctional B φ)
    (fun x hx => by
      obtain ⟨r, hr0, hrφ⟩ := hφ
        ⟨((x : selfAdjoint A) : A), x.property⟩ hx
      show 0 ≤ (φ ⟨((x : selfAdjoint A) : A), x.property⟩).re
      rw [hrφ, Complex.ofReal_re]
      exact hr0)
    (fun y => by
      set r : ℝ := ‖(y : A)‖ with hrdef
      have hsa : IsSelfAdjoint (algebraMap ℝ A r) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact IsSelfAdjoint.smul (star_trivial r) (star_one A)
      have hmem : ((⟨algebraMap ℝ A r, hsa⟩ : selfAdjoint A) : A) ∈ B := by
        show algebraMap ℝ A r ∈ B
        rw [IsScalarTower.algebraMap_apply ℝ ℂ A]
        exact B.algebraMap_mem _
      refine ⟨⟨⟨algebraMap ℝ A r, hsa⟩, hmem⟩, ?_⟩
      rw [mem_positiveCone]
      show 0 ≤ algebraMap ℝ A r + (y : A)
      have h1 : -((y : A)) ≤ algebraMap ℝ A r := by
        have h := (y.property).neg.le_algebraMap_norm_self
        rwa [norm_neg] at h
      have h2 := add_le_add_right h1 (y : A)
      rw [add_neg_cancel] at h2
      rwa [add_comm] at h2)
  exact ⟨g, hg1, fun x hx => hg2 x hx⟩

end Subalgebra

section Reassembly

/-- The self-adjoint real part of an element. -/
def rePart (a : A) : selfAdjoint A :=
  ⟨(2⁻¹ : ℝ) • (a + star a), by
    show star _ = _
    rw [star_real_smul, star_add, star_star, add_comm]⟩

/-- The self-adjoint imaginary part of an element. -/
def imPart (a : A) : selfAdjoint A :=
  ⟨(2⁻¹ : ℝ) • ((-Complex.I) • (a - star a)), by
    show star _ = _
    rw [star_real_smul, star_smul, star_sub, star_star]
    rw [show star (-Complex.I) = Complex.I by simp]
    rw [show Complex.I • ((star a) - a) = (-Complex.I) • (a - star a) by
      rw [← neg_smul_neg, neg_sub]]⟩

@[simp] theorem rePart_coe (a : A) :
    ((rePart a : selfAdjoint A) : A) = (2⁻¹ : ℝ) • (a + star a) :=
  rfl

@[simp] theorem imPart_coe (a : A) :
    ((imPart a : selfAdjoint A) : A)
      = (2⁻¹ : ℝ) • ((-Complex.I) • (a - star a)) :=
  rfl

theorem rePart_add_I_smul_imPart (a : A) :
    ((rePart a : selfAdjoint A) : A)
      + Complex.I • ((imPart a : selfAdjoint A) : A) = a := by
  rw [rePart_coe, imPart_coe]
  rw [smul_comm (Complex.I) ((2⁻¹ : ℝ)) ((-Complex.I) • (a - star a))]
  rw [smul_smul Complex.I (-Complex.I) (a - star a)]
  rw [show Complex.I * -Complex.I = (1 : ℂ) by
    rw [mul_neg, Complex.I_mul_I, neg_neg]]
  rw [one_smul, ← smul_add]
  rw [show a + star a + (a - star a) = (2 : ℝ) • a by
    rw [show ((2 : ℝ) • a) = a + a from two_smul ℝ a]
    abel]
  rw [smul_smul]
  norm_num

theorem rePart_add (a b : A) : rePart (a + b) = rePart a + rePart b := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • (a + b + star (a + b))
      = ((rePart a : selfAdjoint A) : A) + ((rePart b : selfAdjoint A) : A)
  rw [star_add, rePart_coe, rePart_coe, ← smul_add]
  congr 1
  abel

theorem imPart_add (a b : A) : imPart (a + b) = imPart a + imPart b := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • ((-Complex.I) • (a + b - star (a + b)))
      = ((imPart a : selfAdjoint A) : A) + ((imPart b : selfAdjoint A) : A)
  rw [star_add, imPart_coe, imPart_coe, ← smul_add, ← smul_add]
  congr 2
  abel

theorem rePart_real_smul (r : ℝ) (a : A) :
    rePart (r • a) = r • rePart a := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • (r • a + star (r • a)) = r • ((2⁻¹ : ℝ) • (a + star a))
  rw [star_real_smul, ← smul_add, smul_smul, smul_smul, mul_comm]

theorem imPart_real_smul (r : ℝ) (a : A) :
    imPart (r • a) = r • imPart a := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • ((-Complex.I) • (r • a - star (r • a)))
      = r • ((2⁻¹ : ℝ) • ((-Complex.I) • (a - star a)))
  rw [star_real_smul, ← smul_sub, smul_comm (-Complex.I) r (a - star a),
    smul_smul, smul_smul, mul_comm]

theorem rePart_I_smul (a : A) :
    rePart (Complex.I • a) = -imPart a := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • (Complex.I • a + star (Complex.I • a))
      = -((2⁻¹ : ℝ) • ((-Complex.I) • (a - star a)))
  rw [star_smul, show star Complex.I = -Complex.I by simp, ← smul_neg]
  congr 1
  simp only [neg_smul, smul_sub]
  abel

theorem imPart_I_smul (a : A) :
    imPart (Complex.I • a) = rePart a := by
  apply Subtype.ext
  show (2⁻¹ : ℝ) • ((-Complex.I) • (Complex.I • a - star (Complex.I • a)))
      = (2⁻¹ : ℝ) • (a + star a)
  rw [star_smul, show star Complex.I = -Complex.I by simp]
  congr 1
  rw [smul_sub, smul_smul, smul_smul]
  rw [show (-Complex.I) * Complex.I = (1 : ℂ) by
    rw [neg_mul, Complex.I_mul_I, neg_neg]]
  rw [show (-Complex.I) * -Complex.I = (-1 : ℂ) by
    rw [neg_mul_neg, Complex.I_mul_I]]
  rw [one_smul, neg_one_smul, sub_neg_eq_add]

variable (g : (selfAdjoint A) →ₗ[ℝ] ℝ)

/-- The complex functional reassembled from a real functional on the
self-adjoint part. -/
def complexify : A →ₗ[ℂ] ℂ where
  toFun := fun a => (g (rePart a) : ℂ) + Complex.I * (g (imPart a) : ℂ)
  map_add' := fun a b => by
    rw [rePart_add, imPart_add, map_add, map_add]
    push_cast
    ring
  map_smul' := fun c a => by
    show (g (rePart (c • a)) : ℂ) + Complex.I * (g (imPart (c • a)) : ℂ)
        = c * ((g (rePart a) : ℂ) + Complex.I * (g (imPart a) : ℂ))
    have hdecomp : c • a = c.re • a + c.im • (Complex.I • a) := by
      rw [← algebraMap_smul ℂ c.re a,
        ← algebraMap_smul ℂ c.im (Complex.I • a), smul_smul, ← add_smul]
      congr 1
      rw [show (algebraMap ℝ ℂ) c.re = (c.re : ℂ) by simp,
        show (algebraMap ℝ ℂ) c.im = (c.im : ℂ) by simp]
      exact (Complex.re_add_im c).symm
    rw [hdecomp]
    simp only [rePart_add, imPart_add, rePart_real_smul, imPart_real_smul,
      rePart_I_smul, imPart_I_smul, smul_neg, map_add, map_neg, map_smul,
      smul_eq_mul]
    push_cast
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (-(c.im : ℂ) * ((g (imPart a) : ℝ) : ℂ))
      * Complex.I_sq

@[simp] theorem complexify_apply (a : A) :
    complexify g a
      = (g (rePart a) : ℂ) + Complex.I * (g (imPart a) : ℂ) :=
  rfl

variable [PartialOrder A] [StarOrderedRing A]

/-- The reassembled functional is positive when the real functional is
nonnegative on the positive cone. -/
theorem complexify_nonneg
    (hg : ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x)
    {a : A} (ha : 0 ≤ a) :
    ∃ r : ℝ, 0 ≤ r ∧ complexify g a = r := by
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hre : rePart a = ⟨a, hsa⟩ := by
    apply Subtype.ext
    rw [rePart_coe, hsa.star_eq, ← two_smul ℝ a, smul_smul]
    norm_num
  have him : imPart a = 0 := by
    apply Subtype.ext
    rw [imPart_coe, hsa.star_eq, sub_self, smul_zero, smul_zero]
    exact (AddSubgroup.coe_zero _).symm
  refine ⟨g ⟨a, hsa⟩, hg ⟨a, hsa⟩ ha, ?_⟩
  rw [complexify_apply, hre, him, map_zero]
  push_cast
  ring

end Reassembly

section Main

variable [PartialOrder A] [StarOrderedRing A]
variable {B : StarSubalgebra ℂ A} {φ : B →ₗ[ℂ] ℂ}

/-- The reassembled extension agrees with `φ` on the subalgebra. -/
theorem complexify_extends
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r)
    (g : (selfAdjoint A) →ₗ[ℝ] ℝ)
    (hg : ∀ x : (realPartialFunctional B φ).domain,
      g x = (realPartialFunctional B φ) x)
    (b : B) : complexify g (b : A) = φ b := by
  have hre_mem : ((rePart (b : A) : selfAdjoint A) : A) ∈ B := by
    rw [rePart_coe, ← algebraMap_smul ℂ (2⁻¹ : ℝ) ((b : A) + star (b : A))]
    exact B.smul_mem (add_mem b.property (star_mem b.property)) _
  have him_mem : ((imPart (b : A) : selfAdjoint A) : A) ∈ B := by
    rw [imPart_coe,
      ← algebraMap_smul ℂ (2⁻¹ : ℝ) ((-Complex.I) • ((b : A) - star (b : A)))]
    exact B.smul_mem (B.smul_mem
      (sub_mem b.property (star_mem b.property)) _) _
  set bre : B := ⟨((rePart (b : A) : selfAdjoint A) : A), hre_mem⟩
  set bim : B := ⟨((imPart (b : A) : selfAdjoint A) : A), him_mem⟩
  have hgre : (g (rePart (b : A)) : ℂ) = φ bre := by
    have h1 := hg ⟨rePart (b : A), hre_mem⟩
    rw [h1]
    exact (phi_real_of_isSelfAdjoint B φ hφ
      (selfAdjoint.mem_iff.mp (rePart (b : A)).property)).symm
  have hgim : (g (imPart (b : A)) : ℂ) = φ bim := by
    have h1 := hg ⟨imPart (b : A), him_mem⟩
    rw [h1]
    exact (phi_real_of_isSelfAdjoint B φ hφ
      (selfAdjoint.mem_iff.mp (imPart (b : A)).property)).symm
  have hsum : bre + Complex.I • bim = b := by
    apply Subtype.ext
    show ((rePart (b : A) : selfAdjoint A) : A)
        + Complex.I • ((imPart (b : A) : selfAdjoint A) : A) = (b : A)
    exact rePart_add_I_smul_imPart (b : A)
  rw [complexify_apply, hgre, hgim, ← smul_eq_mul, ← map_smul, ← map_add,
    hsum]

/-- **Positive extension**: a functional on a unital star subalgebra that
is nonnegative on ambient positives extends to the whole algebra with the
same positivity. -/
theorem exists_positive_extension
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ Φ : A →ₗ[ℂ] ℂ, (∀ b : B, Φ b = φ b) ∧
      ∀ a : A, 0 ≤ a → ∃ r : ℝ, 0 ≤ r ∧ Φ a = r := by
  obtain ⟨g, hg1, hg2⟩ := exists_real_extension B φ hφ
  exact ⟨complexify g, complexify_extends hφ g hg1,
    fun a ha => complexify_nonneg g hg2 ha⟩

/-- The extension, packaged as a positive linear map ready for GNS. -/
theorem exists_positiveLinearMap_extension
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ Φ : A →ₚ[ℂ] ℂ, ∀ b : B, Φ b = φ b := by
  obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_positive_extension hφ
  have hmono : Monotone Φ := by
    intro a b hab
    obtain ⟨r, hr0, hr⟩ := hΦ2 (b - a) (sub_nonneg.mpr hab)
    rw [map_sub] at hr
    have hre := congrArg Complex.re hr
    have him := congrArg Complex.im hr
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im] at him
    rw [Complex.le_def]
    constructor
    · linarith
    · linarith
  exact ⟨⟨Φ, hmono⟩, hΦ1⟩

end Main

end

end StateExtension
end GroupApproximation
