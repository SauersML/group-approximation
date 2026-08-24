import GroupApproximation.Sofic.UltraproductKazhdanProjection
import GroupApproximation.Sofic.UltraproductScaledTransport

/-!
# KT.02 and KT.04: the Hilbert-space ultraproduct `K_ω` and the action of `B_ω`

This module builds the object that the ultraproduct proof of
the Kazhdan transport result in `non_mf_groups_exist.tex` calls `K_ω`, and
the action of the norm ultraproduct `B_ω` on it.  Anchors are by label and by
the italicized paragraph headings of the printed proof
(`\emph{The adjoint model.}`, `\emph{The ultraproduct.}`,
`\emph{The Kazhdan projection.}`,
`\emph{One-sided compression and finiteness.}`); line numbers are not cited
because the manuscript is under concurrent edit.

Nothing in this repository constructed `K_ω` before this file.
`Sofic/UltraproductAdjointAmbient.lean` builds `B_ω` and the homomorphism
`π`, and says so explicitly ("The Hilbert-space ultraproduct `K_ω` is **not**
constructed here"); `Sofic/UltraproductKazhdanProjection.lean` builds the
Kazhdan projection inside an abstract C-star algebra.  Consequently both
`UltraproductAdjointModel` and `WeightedUltraproductAdjointModel` were
*bundles nothing constructs*.  This file, together with
`Sofic/UltraproductModelConstructionAssembly.lean`, removes that.

## What `K_ω` is here, and what it is not

For a family `(Y n)` of nonempty finite models and a nonnegative weight
`w : ℕ → ℝ`, the manuscript's coordinate space is `M_{Y n}(ℂ)` carrying the
renormalized inner product `⟨x, y⟩ = Tr(y* x) / w n`, whose squared norm is
`matMass x / w n`.  Its ultraproduct along a free ultrafilter `ω` is, as a
set and as a complex vector space,

`K_ω = {families of mass `O(w n)`} / {families with mass `o(w n)` along ω}`,

and that is exactly `Vec` below: the quotient of the submodule
`massBounded Y w` of `∀ n, M_{Y n}(ℂ)` by the submodule of families that are
`ω`-null at the weight.  This is the honest underlying module of the
Hilbert-space ultraproduct.

**What is deliberately not built:** the inner product
`⟨[ξ], [η]⟩ = lim_ω Tr(η_n* ξ_n)/w n` and the resulting Hilbert-space
structure.  Every field of the manuscript's ultraproduct interface -- the
action, the class map, the class-equality criterion, and the fixed-vector
description of the Kazhdan projection -- is a statement about the
*coordinate* masses and about the algebra `B_ω`, so no norm on `Vec` is used
anywhere below, and none is claimed.  The docstrings never call `Vec` a
Hilbert space.

## What acts on it

`B(K_n)` is a matrix algebra on the doubled index `Y n × Y n`, so the
manuscript's `B_ω = ∏_ω B(K_n)` is the repo's `NormMatrixCStarCorona` on
`fun n ↦ (doubleModel (Y n) : Type)` (`AdjointCorona`).  That corona is taken
along the cofinite filter, which is the realization of `ω` already fixed by
`Sofic/UltraproductDedekindFinite.lean`, where KT.06 is proved.  The action
of a cofinite corona class on an `ω`-ultraproduct vector is well defined
because a cofinite-null operator sequence is `ω`-null for every `ω` below the
cofinite filter; the resulting action factors through `∏_ω B(K_n)`, and this
is the one place where the chain uses the cofinite corona rather than the
literal `ω`-corona.  See the report accompanying this file.

The action is built as a genuine `ℂ`-algebra homomorphism
`AdjointCorona Y → Module.End ℂ (Vec Y w ω)`.  That is not cosmetic:
`ℂ`-linearity **in the algebra argument** is exactly what turns the Kazhdan
spectral gap into the statement `Fix ⊆ ran P` (`act_P_iff` below), through
the resolvent factorisation `1 - P = cfc (gapResolvent c) h · (1 - h)` of
`Analysis/KazhdanProjectionAbsorption.lean`.
-/

namespace GroupApproximation
namespace UltraproductModelConstruction

open Filter Matrix
open ScaledKazhdanTransport UltraproductScaledTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Coordinates: row-major vectorization and the mass estimate

`K_n = M_{Y n}(ℂ)` is `ℂ^{Y n × Y n}` in row-major coordinates, and an
operator on it is a matrix on `Y n × Y n`.  The three lemmas here are the
whole of the coordinate bookkeeping. -/

section Coordinates

variable (Z : FiniteModel)

/-- Row-major vectorization is inverted by `rowMat`. -/
theorem rowMat_rowVec (X : Matrix Z Z ℂ) : rowMat (rowVec X) = X := by
  ext i j
  rfl

/-- The Frobenius mass of a matrix read off a pair-coordinate vector is the
Euclidean mass of that vector. -/
theorem matMass_rowMat (v : Z × Z → ℂ) :
    matMass (rowMat v) = ∑ p : Z × Z, Complex.normSq (v p) := by
  have h := sum_normSq_rowVec (Y := (Z : Type)) (rowMat v)
  rw [rowVec_rowMat] at h
  exact h.symm

/-- **The mass estimate behind the action.**  An operator on `K_n`, i.e. a
matrix on the doubled index, moves the Frobenius mass by at most the square
of its `l²` operator norm.  Because the weight `w n` divides both sides, this
single estimate is what makes the action well defined at *every* weight. -/
theorem matMass_rowMat_mulVec_le
    (A : Matrix (doubleModel Z) (doubleModel Z) ℂ) (xi : Matrix Z Z ℂ) :
    matMass (rowMat (A *ᵥ rowVec xi)) ≤ ‖A‖ ^ 2 * matMass xi := by
  rw [matMass_rowMat Z (A *ᵥ rowVec xi)]
  have hR : matMass xi = ∑ p : Z × Z, Complex.normSq (rowVec xi p) :=
    (sum_normSq_rowVec (Y := (Z : Type)) xi).symm
  rw [hR]
  exact KazhdanCornerMatrices.sum_normSq_mulVec_le_general A (rowVec xi)

/-- In row-major coordinates the operator `conjDouble V` is the adjoint
action `ξ ↦ V ξ V*`.  This is manuscript step KT.01, in the form the action
consumes. -/
theorem rowMat_conjDouble_mulVec (V : Matrix Z Z ℂ) (xi : Matrix Z Z ℂ) :
    rowMat (conjDouble V *ᵥ rowVec xi) = V * xi * Vᴴ := by
  rw [conjDouble_mulVec_rowVec, rowMat_rowVec]

end Coordinates

/-! ## The weight, clipped

`WeightNull` at a weight that goes negative somewhere is not closed under
addition of the zero family, so the null families form a submodule only for a
nonnegative weight.  Rather than make the *type* `K_ω` depend on a proof of
nonnegativity, the submodule is defined at the clipped weight `max (w n) 0`,
which agrees with `w` under the manuscript's standing hypothesis
`0 ≤ w n`. -/

/-- The weight clipped to be nonnegative. -/
def clipWeight (w : ℕ → ℝ) : ℕ → ℝ := fun n ↦ max (w n) 0

theorem clipWeight_nonneg (w : ℕ → ℝ) (n : ℕ) : 0 ≤ clipWeight w n :=
  le_max_right _ _

theorem clipWeight_eq (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    clipWeight w n = w n :=
  max_eq_left (hw n)

/-! ## KT.02: the ultraproduct `K_ω` -/

section Ultraproduct

variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-- A family of coordinate matrices. -/
abbrev MatFam (Y : ℕ → FiniteModel) : Type := ∀ n, Matrix (Y n) (Y n) ℂ

/-- **The numerator of `K_ω`.**  The families whose Frobenius mass is
`O(w n)`, i.e. those that are bounded for the renormalized coordinate norms.
This is the manuscript's mass bound `Tr(x_n* x_n) ≤ C w_n`, existentially
quantified over the constant. -/
def massBounded : Submodule ℂ (MatFam Y) where
  carrier := {ξ | ∃ C : ℝ, ∀ n, matMass (ξ n) ≤ C * w n}
  zero_mem' := by
    refine ⟨0, fun n ↦ ?_⟩
    show matMass (0 : Matrix (Y n) (Y n) ℂ) ≤ 0 * w n
    rw [matMass_zero, zero_mul]
  add_mem' := by
    rintro a b ⟨Ca, hA⟩ ⟨Cb, hB⟩
    refine ⟨2 * Ca + 2 * Cb, fun n ↦ ?_⟩
    show matMass (a n + b n) ≤ (2 * Ca + 2 * Cb) * w n
    have h1 : matMass (a n + b n) ≤ 2 * matMass (a n) + 2 * matMass (b n) :=
      matMass_add_le _ _
    have h2 := hA n
    have h3 := hB n
    nlinarith [h1, h2, h3]
  smul_mem' := by
    rintro c a ⟨Ca, hA⟩
    refine ⟨Complex.normSq c * Ca, fun n ↦ ?_⟩
    show matMass (c • a n) ≤ Complex.normSq c * Ca * w n
    rw [matMass_smul]
    have h1 : Complex.normSq c * matMass (a n)
        ≤ Complex.normSq c * (Ca * w n) :=
      mul_le_mul_of_nonneg_left (hA n) (Complex.normSq_nonneg c)
    calc Complex.normSq c * matMass (a n)
        ≤ Complex.normSq c * (Ca * w n) := h1
      _ = Complex.normSq c * Ca * w n := by ring

theorem mem_massBounded_iff (ξ : MatFam Y) :
    ξ ∈ massBounded Y w ↔ ∃ C : ℝ, ∀ n, matMass (ξ n) ≤ C * w n :=
  Iff.rfl

/-- A family with the manuscript's mass bound lies in the numerator. -/
theorem weightBounded_mem_massBounded {C : ℝ} {ξ : MatFam Y}
    (h : WeightBounded Y w C ξ) : ξ ∈ massBounded Y w :=
  ⟨C, h⟩

/-- **The denominator of `K_ω`.**  The families that are null at the weight
along `ω`: for every `ε > 0`, eventually `Tr|ξ_n|² ≤ ε w_n`.  It is stated at
the clipped weight so that it is a submodule with no hypothesis on `w`;
`mem_massNull_iff` identifies it with `WeightNull` whenever `0 ≤ w`. -/
def massNull : Submodule ℂ (MatFam Y) where
  carrier := {ξ | WeightNull Y (clipWeight w) (ω : Filter ℕ) ξ}
  zero_mem' := by
    intro ε hε
    refine Eventually.of_forall fun n ↦ ?_
    show matMass (0 : Matrix (Y n) (Y n) ℂ) ≤ ε * clipWeight w n
    rw [matMass_zero]
    exact mul_nonneg hε.le (clipWeight_nonneg w n)
  add_mem' := by
    intro a b ha hb ε hε
    have ha' : ∀ᶠ n in (ω : Filter ℕ),
        matMass (a n) ≤ ε / 4 * clipWeight w n := ha (ε / 4) (by linarith)
    have hb' : ∀ᶠ n in (ω : Filter ℕ),
        matMass (b n) ≤ ε / 4 * clipWeight w n := hb (ε / 4) (by linarith)
    filter_upwards [ha', hb'] with n hna hnb
    show matMass (a n + b n) ≤ ε * clipWeight w n
    have h1 : matMass (a n + b n) ≤ 2 * matMass (a n) + 2 * matMass (b n) :=
      matMass_add_le _ _
    linarith
  smul_mem' := by
    intro c a ha ε hε
    have hden : (0 : ℝ) < Complex.normSq c + 1 := by
      nlinarith [Complex.normSq_nonneg c]
    have ha' : ∀ᶠ n in (ω : Filter ℕ),
        matMass (a n) ≤ ε / (Complex.normSq c + 1) * clipWeight w n :=
      ha (ε / (Complex.normSq c + 1)) (div_pos hε hden)
    filter_upwards [ha'] with n hn
    show matMass (c • a n) ≤ ε * clipWeight w n
    rw [matMass_smul]
    have hnn : (0 : ℝ) ≤ Complex.normSq c := Complex.normSq_nonneg c
    have hcw : (0 : ℝ) ≤ clipWeight w n := clipWeight_nonneg w n
    have hεw : (0 : ℝ) ≤ ε * clipWeight w n := mul_nonneg hε.le hcw
    have hratio : Complex.normSq c / (Complex.normSq c + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    calc Complex.normSq c * matMass (a n)
        ≤ Complex.normSq c *
            (ε / (Complex.normSq c + 1) * clipWeight w n) :=
          mul_le_mul_of_nonneg_left hn hnn
      _ = (Complex.normSq c / (Complex.normSq c + 1)) *
            (ε * clipWeight w n) := by ring
      _ ≤ 1 * (ε * clipWeight w n) :=
          mul_le_mul_of_nonneg_right hratio hεw
      _ = ε * clipWeight w n := one_mul _

/-- At a nonnegative weight the denominator is exactly the manuscript's
defect condition along `ω`. -/
theorem mem_massNull_iff (hw : ∀ n, 0 ≤ w n) (ξ : MatFam Y) :
    ξ ∈ massNull Y w ω ↔ WeightNull Y w (ω : Filter ℕ) ξ := by
  have hclip : ∀ n, clipWeight w n = w n := clipWeight_eq w hw
  constructor
  · intro h ε hε
    have h' : ∀ᶠ n in (ω : Filter ℕ),
        matMass (ξ n) ≤ ε * clipWeight w n := h ε hε
    filter_upwards [h'] with n hn
    rwa [hclip n] at hn
  · intro h ε hε
    have h' : ∀ᶠ n in (ω : Filter ℕ), matMass (ξ n) ≤ ε * w n := h ε hε
    filter_upwards [h'] with n hn
    rw [hclip n]
    exact hn

/-- The denominator, viewed inside the numerator. -/
def nullIn : Submodule ℂ (massBounded Y w) :=
  Submodule.comap (massBounded Y w).subtype (massNull Y w ω)

theorem mem_nullIn_iff (ξ : massBounded Y w) :
    ξ ∈ nullIn Y w ω ↔ (ξ : MatFam Y) ∈ massNull Y w ω :=
  Iff.rfl

/-- **KT.02.**  The ultraproduct `K_ω` of the renormalized coordinate spaces
`K_n = (M_{Y n}(ℂ), Tr(y* x)/w n)` along `ω`: mass-bounded families modulo
families that are null at the weight along `ω`.

This is the underlying complex vector space of the Hilbert-space
ultraproduct.  Its inner product is not constructed, and no field of the
manuscript's interface refers to one. -/
abbrev Vec : Type := (massBounded Y w) ⧸ (nullIn Y w ω)

/-- **The class `[ξ_n]_ω`.**  Defined on every family, by the manuscript's
recipe on the mass-bounded ones and by `0` elsewhere; the manuscript only
ever forms `[ξ_n]_ω` under its mass bound, and every statement below about
`cls` either assumes that bound or is invariant under the convention. -/
def cls (ξ : MatFam Y) : Vec Y w ω :=
  @dite (Vec Y w ω) (ξ ∈ massBounded Y w) (Classical.dec _)
    (fun h ↦ Submodule.Quotient.mk ⟨ξ, h⟩) (fun _ ↦ 0)

theorem cls_of_mem {ξ : MatFam Y} (h : ξ ∈ massBounded Y w) :
    cls Y w ω ξ = Submodule.Quotient.mk ⟨ξ, h⟩ := by
  unfold cls
  exact dif_pos h

theorem cls_of_not_mem {ξ : MatFam Y} (h : ξ ∉ massBounded Y w) :
    cls Y w ω ξ = 0 := by
  unfold cls
  exact dif_neg h

/-- **KT.02 and KT.04, the class-equality criterion.**  Two families carrying
the manuscript's mass bound have the same ultraproduct class exactly when
their difference is null at the weight along `ω`. -/
theorem cls_eq_iff_weightNull (hw : ∀ n, 0 ≤ w n) (C : ℝ)
    (ξ η : MatFam Y) (hξ : WeightBounded Y w C ξ) (hη : WeightBounded Y w C η) :
    cls Y w ω ξ = cls Y w ω η ↔
      WeightNull Y w (ω : Filter ℕ) (fun n ↦ ξ n - η n) := by
  have hξm : ξ ∈ massBounded Y w := weightBounded_mem_massBounded Y w hξ
  have hηm : η ∈ massBounded Y w := weightBounded_mem_massBounded Y w hη
  rw [cls_of_mem Y w ω hξm, cls_of_mem Y w ω hηm]
  rw [Submodule.Quotient.eq (nullIn Y w ω)]
  rw [mem_nullIn_iff]
  have hcoe : (((⟨ξ, hξm⟩ : massBounded Y w) - ⟨η, hηm⟩ : massBounded Y w) :
      MatFam Y) = ξ - η := rfl
  rw [hcoe]
  rw [mem_massNull_iff Y w ω hw]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    exact hn
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    exact hn

end Ultraproduct

/-! ## KT.03: the algebra `B_ω`, and its coordinatewise action

`B(K_n)` is the matrix algebra on the doubled index `Y n × Y n`, so the norm
ultraproduct of the `B(K_n)` is the repo's norm-matrix C-star corona on that
index.  The nonemptiness instance the corona needs is available as soon as
each `Y n` is nonempty. -/

section Action

-- Nonemptiness of the coordinate models is *not* introduced here: almost
-- everything from `applyFam` to `actQ_eq_zero_of_isC0` works with bounded
-- operator sequences and never forms the corona, so carrying the instance
-- through that block would leave it unused in almost every one of those
-- declarations.  It is introduced below as a section variable immediately
-- before `coronaLift`, which is the first declaration that names
-- `AdjointCorona Y`.
--
-- The exceptions are the four statements that name `1` or a scalar multiple
-- of a bounded sequence (`applyFam_one`, `applyFam_smul_left`, `actQ_one`,
-- `actQ_smul`).  The unit and the `ℂ`-algebra structure of
-- `lp (fun n ↦ Matrix (DblIdx Y n) (DblIdx Y n) ℂ) ∞` come from
-- `lp.inftyRing` and `lp.instAlgebra`, both of which want
-- `NormOneClass (Matrix (DblIdx Y n) (DblIdx Y n) ℂ)`; with the l²-operator
-- norm that holds only because the matrix algebra is nontrivial, i.e. only
-- when the index is nonempty.  Those four carry the instance as their own
-- binder rather than forcing it on the whole block.
variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-- The doubled finite models `Y n × Y n`. -/
abbrev DblFam (Y : ℕ → FiniteModel) : ℕ → FiniteModel :=
  fun n ↦ doubleModel (Y n)

/-- The doubled coordinate index `Y n × Y n`, on which the operators of
`K_n` are matrices. -/
abbrev DblIdx (Y : ℕ → FiniteModel) : ℕ → Type :=
  fun n ↦ ((DblFam Y n : FiniteModel) : Type)

instance instNonemptyDblIdx (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (n : ℕ) : Nonempty (DblIdx Y n) := by
  show Nonempty ((Y n) × (Y n))
  infer_instance

/-- **KT.03.**  The manuscript's `B_ω = ∏_ω B(K_n)`, realized as the
norm-matrix C-star corona on the doubled index.  Its Dedekind finiteness --
manuscript step KT.06 -- is the instance
`normMatrixCStarCorona_isDedekindFiniteMonoid`. -/
abbrev AdjointCorona (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] : Type :=
  NormMatrixCStarCorona (DblIdx Y)

/-- **KT.03, on representatives.**  An operator sequence acts on a family of
coordinate matrices coordinatewise, through row-major vectorization. -/
def applyFam (a : BoundedMatrixSequence (DblIdx Y)) (ξ : MatFam Y) :
    MatFam Y :=
  fun n ↦ rowMat (a n *ᵥ rowVec (ξ n))

@[simp] theorem applyFam_apply (a : BoundedMatrixSequence (DblIdx Y))
    (ξ : MatFam Y) (n : ℕ) :
    applyFam Y a ξ n = rowMat (a n *ᵥ rowVec (ξ n)) := rfl

theorem matMass_applyFam_le (a : BoundedMatrixSequence (DblIdx Y))
    (ξ : MatFam Y) (n : ℕ) :
    matMass (applyFam Y a ξ n) ≤ ‖a n‖ ^ 2 * matMass (ξ n) :=
  matMass_rowMat_mulVec_le (Y n) (a n) (ξ n)

/-! ### Linearity in the vector -/

theorem applyFam_zero (a : BoundedMatrixSequence (DblIdx Y)) :
    applyFam Y a (0 : MatFam Y) = 0 := by
  funext n
  show rowMat (a n *ᵥ rowVec (0 : Matrix (Y n) (Y n) ℂ)) = 0
  have hrv : rowVec (0 : Matrix (Y n) (Y n) ℂ) = 0 := by
    funext p
    rfl
  rw [hrv, Matrix.mulVec_zero]
  ext i j
  rfl

theorem applyFam_add (a : BoundedMatrixSequence (DblIdx Y))
    (ξ η : MatFam Y) :
    applyFam Y a (ξ + η) = applyFam Y a ξ + applyFam Y a η := by
  funext n
  show rowMat (a n *ᵥ rowVec (ξ n + η n))
      = rowMat (a n *ᵥ rowVec (ξ n)) + rowMat (a n *ᵥ rowVec (η n))
  have hrv : rowVec (ξ n + η n) = rowVec (ξ n) + rowVec (η n) := by
    funext p
    rfl
  rw [hrv, Matrix.mulVec_add]
  ext i j
  rfl

theorem applyFam_smul (a : BoundedMatrixSequence (DblIdx Y)) (c : ℂ)
    (ξ : MatFam Y) :
    applyFam Y a (c • ξ) = c • applyFam Y a ξ := by
  funext n
  show rowMat (a n *ᵥ rowVec (c • ξ n)) = c • rowMat (a n *ᵥ rowVec (ξ n))
  have hrv : rowVec (c • ξ n) = c • rowVec (ξ n) := by
    funext p
    rfl
  rw [hrv, Matrix.mulVec_smul]
  ext i j
  rfl

/-! ### Linearity and multiplicativity in the operator -/

theorem applyFam_zero_left (ξ : MatFam Y) :
    applyFam Y (0 : BoundedMatrixSequence (DblIdx Y)) ξ = 0 := by
  funext n
  have h0 : (0 : BoundedMatrixSequence (DblIdx Y)) n = 0 := by
    ext i j
    rfl
  show rowMat ((0 : BoundedMatrixSequence (DblIdx Y)) n *ᵥ rowVec (ξ n)) = 0
  rw [h0, Matrix.zero_mulVec]
  ext i j
  rfl

theorem applyFam_add_left (a b : BoundedMatrixSequence (DblIdx Y))
    (ξ : MatFam Y) :
    applyFam Y (a + b) ξ = applyFam Y a ξ + applyFam Y b ξ := by
  funext n
  have hab : (a + b) n = a n + b n := by
    ext i j
    rfl
  show rowMat ((a + b) n *ᵥ rowVec (ξ n))
      = rowMat (a n *ᵥ rowVec (ξ n)) + rowMat (b n *ᵥ rowVec (ξ n))
  rw [hab, Matrix.add_mulVec]
  ext i j
  rfl

theorem applyFam_smul_left [∀ n, Nonempty (Y n)] (c : ℂ)
    (a : BoundedMatrixSequence (DblIdx Y)) (ξ : MatFam Y) :
    applyFam Y (c • a) ξ = c • applyFam Y a ξ := by
  funext n
  have hca : (c • a) n = c • a n := by
    ext i j
    rfl
  show rowMat ((c • a) n *ᵥ rowVec (ξ n)) = c • rowMat (a n *ᵥ rowVec (ξ n))
  rw [hca, Matrix.smul_mulVec]
  ext i j
  rfl

theorem applyFam_one [∀ n, Nonempty (Y n)] (ξ : MatFam Y) :
    applyFam Y (1 : BoundedMatrixSequence (DblIdx Y)) ξ = ξ := by
  funext n
  have h1 : (1 : BoundedMatrixSequence (DblIdx Y)) n = 1 := by
    ext i j
    rfl
  show rowMat ((1 : BoundedMatrixSequence (DblIdx Y)) n *ᵥ rowVec (ξ n)) = ξ n
  rw [h1, Matrix.one_mulVec, rowMat_rowVec]

theorem applyFam_mul (a b : BoundedMatrixSequence (DblIdx Y))
    (ξ : MatFam Y) :
    applyFam Y (a * b) ξ = applyFam Y a (applyFam Y b ξ) := by
  funext n
  have hab : (a * b) n = a n * b n := by
    ext i j
    rfl
  show rowMat ((a * b) n *ᵥ rowVec (ξ n))
      = rowMat (a n *ᵥ rowVec (rowMat (b n *ᵥ rowVec (ξ n))))
  rw [hab, rowVec_rowMat, Matrix.mulVec_mulVec]

/-! ### The action preserves the numerator and the denominator -/

theorem applyFam_mem_massBounded (a : BoundedMatrixSequence (DblIdx Y))
    {ξ : MatFam Y} (hξ : ξ ∈ massBounded Y w) :
    applyFam Y a ξ ∈ massBounded Y w := by
  obtain ⟨C, hC⟩ := hξ
  refine ⟨‖a‖ ^ 2 * C, fun n ↦ ?_⟩
  have hcoord : ‖a n‖ ≤ ‖a‖ := (lp.isLUB_norm a).1 ⟨n, rfl⟩
  have hsq : ‖a n‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
    nlinarith
  calc matMass (applyFam Y a ξ n)
      ≤ ‖a n‖ ^ 2 * matMass (ξ n) := matMass_applyFam_le Y a ξ n
    _ ≤ ‖a‖ ^ 2 * (C * w n) :=
        mul_le_mul hsq (hC n) (matMass_nonneg _) (sq_nonneg _)
    _ = ‖a‖ ^ 2 * C * w n := by ring

theorem applyFam_mem_massNull (a : BoundedMatrixSequence (DblIdx Y))
    {ξ : MatFam Y} (hξ : ξ ∈ massNull Y w ω) :
    applyFam Y a ξ ∈ massNull Y w ω := by
  intro ε hε
  have hden : (0 : ℝ) < ‖a‖ ^ 2 + 1 := by positivity
  have hξ' : ∀ᶠ n in (ω : Filter ℕ),
      matMass (ξ n) ≤ ε / (‖a‖ ^ 2 + 1) * clipWeight w n :=
    hξ (ε / (‖a‖ ^ 2 + 1)) (div_pos hε hden)
  filter_upwards [hξ'] with n hn
  show matMass (applyFam Y a ξ n) ≤ ε * clipWeight w n
  have hcoord : ‖a n‖ ≤ ‖a‖ := (lp.isLUB_norm a).1 ⟨n, rfl⟩
  have hsq : ‖a n‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
    nlinarith
  have hcw : (0 : ℝ) ≤ clipWeight w n := clipWeight_nonneg w n
  have hεw : (0 : ℝ) ≤ ε * clipWeight w n := mul_nonneg hε.le hcw
  have hratio : ‖a‖ ^ 2 / (‖a‖ ^ 2 + 1) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith [sq_nonneg ‖a‖])
  calc matMass (applyFam Y a ξ n)
      ≤ ‖a n‖ ^ 2 * matMass (ξ n) := matMass_applyFam_le Y a ξ n
    _ ≤ ‖a‖ ^ 2 * (ε / (‖a‖ ^ 2 + 1) * clipWeight w n) :=
        mul_le_mul hsq hn (matMass_nonneg _) (sq_nonneg _)
    _ = (‖a‖ ^ 2 / (‖a‖ ^ 2 + 1)) * (ε * clipWeight w n) := by ring
    _ ≤ 1 * (ε * clipWeight w n) := mul_le_mul_of_nonneg_right hratio hεw
    _ = ε * clipWeight w n := one_mul _

/-- **The action descends to the corona.**  A sequence of operators whose
norms vanish along the cofinite filter annihilates every mass-bounded family
in the ultraproduct, for any ultrafilter refining the cofinite filter.  This
is exactly what makes the corona -- rather than the bounded sequences -- act
on `K_ω`. -/
theorem applyFam_mem_massNull_of_isC0 (hw : ∀ n, 0 ≤ w n)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {a : BoundedMatrixSequence (DblIdx Y)}
    (ha : IsNullMatrixSequence (DblIdx Y) cofinite a)
    {ξ : MatFam Y} (hξ : ξ ∈ massBounded Y w) :
    applyFam Y a ξ ∈ massNull Y w ω := by
  obtain ⟨C, hC⟩ := hξ
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : (0 : ℝ) ≤ C' := le_max_right _ _
  have hCC' : ∀ n, matMass (ξ n) ≤ C' * w n := fun n ↦
    le_trans (hC n) (mul_le_mul_of_nonneg_right (le_max_left C 0) (hw n))
  intro ε hε
  have hden : (0 : ℝ) < C' + 1 := by linarith
  have hδ : (0 : ℝ) < min 1 (ε / (C' + 1)) :=
    lt_min one_pos (div_pos hε hden)
  have hcof : ∀ᶠ n in Filter.cofinite, ‖a n‖ < min 1 (ε / (C' + 1)) := by
    have h := (Metric.tendsto_nhds.mp ha) _ hδ
    exact h.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_norm] using hn
  filter_upwards [hω hcof] with n hn
  show matMass (applyFam Y a ξ n) ≤ ε * clipWeight w n
  rw [clipWeight_eq w hw n]
  have h2 : ‖a n‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
  have h3 : ‖a n‖ ≤ ε / (C' + 1) :=
    le_of_lt (lt_of_lt_of_le hn (min_le_right _ _))
  have h0 : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
  have h4 : ‖a n‖ ^ 2 ≤ ε / (C' + 1) := by nlinarith
  have hquot : (0 : ℝ) ≤ ε / (C' + 1) := le_of_lt (div_pos hε hden)
  have hle : ε / (C' + 1) * C' ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  calc matMass (applyFam Y a ξ n)
      ≤ ‖a n‖ ^ 2 * matMass (ξ n) := matMass_applyFam_le Y a ξ n
    _ ≤ (ε / (C' + 1)) * (C' * w n) :=
        mul_le_mul h4 (hCC' n) (matMass_nonneg _) hquot
    _ = (ε / (C' + 1) * C') * w n := by ring
    _ ≤ ε * w n := mul_le_mul_of_nonneg_right hle (hw n)

/-! ### The action as an endomorphism of `K_ω` -/

/-- The action on the numerator. -/
def actSub (a : BoundedMatrixSequence (DblIdx Y)) :
    massBounded Y w →ₗ[ℂ] massBounded Y w where
  toFun ξ := ⟨applyFam Y a (ξ : MatFam Y), applyFam_mem_massBounded Y w a ξ.2⟩
  map_add' ξ η := Subtype.ext (applyFam_add Y a (ξ : MatFam Y) (η : MatFam Y))
  map_smul' c ξ := Subtype.ext (applyFam_smul Y a c (ξ : MatFam Y))

@[simp] theorem actSub_coe (a : BoundedMatrixSequence (DblIdx Y))
    (ξ : massBounded Y w) :
    ((actSub Y w a ξ : massBounded Y w) : MatFam Y)
      = applyFam Y a (ξ : MatFam Y) := rfl

theorem nullIn_le_comap (a : BoundedMatrixSequence (DblIdx Y)) :
    nullIn Y w ω ≤ Submodule.comap (actSub Y w a) (nullIn Y w ω) := by
  intro ξ hξ
  exact applyFam_mem_massNull Y w ω a hξ

/-- The action of an operator sequence on the ultraproduct. -/
def actQ (a : BoundedMatrixSequence (DblIdx Y)) :
    Vec Y w ω →ₗ[ℂ] Vec Y w ω :=
  Submodule.mapQ (nullIn Y w ω) (nullIn Y w ω) (actSub Y w a)
    (nullIn_le_comap Y w ω a)

@[simp] theorem actQ_mk (a : BoundedMatrixSequence (DblIdx Y))
    (ξ : massBounded Y w) :
    actQ Y w ω a (Submodule.Quotient.mk ξ)
      = Submodule.Quotient.mk (actSub Y w a ξ) :=
  Submodule.mapQ_apply _ _ _ ξ

/-- Two endomorphisms of the ultraproduct agree once they agree on classes. -/
theorem vec_linearMap_ext {f g : Vec Y w ω →ₗ[ℂ] Vec Y w ω}
    (h : ∀ ξ : massBounded Y w,
      f (Submodule.Quotient.mk ξ) = g (Submodule.Quotient.mk ξ)) :
    f = g := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact h ξ

theorem actQ_one [∀ n, Nonempty (Y n)] : actQ Y w ω 1 = LinearMap.id := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (applyFam_one Y _))

theorem actQ_mul (a b : BoundedMatrixSequence (DblIdx Y)) :
    actQ Y w ω (a * b) = (actQ Y w ω a).comp (actQ Y w ω b) := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk, LinearMap.comp_apply, actQ_mk, actQ_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (applyFam_mul Y a b _))

theorem actQ_add (a b : BoundedMatrixSequence (DblIdx Y)) :
    actQ Y w ω (a + b) = actQ Y w ω a + actQ Y w ω b := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk, LinearMap.add_apply, actQ_mk, actQ_mk,
    ← Submodule.Quotient.mk_add]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (applyFam_add_left Y a b _))

theorem actQ_smul [∀ n, Nonempty (Y n)] (c : ℂ)
    (a : BoundedMatrixSequence (DblIdx Y)) :
    actQ Y w ω (c • a) = c • actQ Y w ω a := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk, LinearMap.smul_apply, actQ_mk, ← Submodule.Quotient.mk_smul]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (applyFam_smul_left Y c a _))

theorem actQ_zero : actQ Y w ω 0 = 0 := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk, LinearMap.zero_apply]
  rw [show ((actSub Y w 0 ξ : massBounded Y w)) = 0 from
    Subtype.ext (applyFam_zero_left Y _)]
  exact Submodule.Quotient.mk_zero _

theorem actQ_sub (a b : BoundedMatrixSequence (DblIdx Y)) :
    actQ Y w ω (a - b) = actQ Y w ω a - actQ Y w ω b := by
  have h : actQ Y w ω (a - b) + actQ Y w ω b = actQ Y w ω a := by
    rw [← actQ_add]
    congr 1
    abel
  rw [← h]
  abel

/-- A cofinite-null operator sequence acts as zero on the ultraproduct. -/
theorem actQ_eq_zero_of_isC0 (hw : ∀ n, 0 ≤ w n)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {a : BoundedMatrixSequence (DblIdx Y)}
    (ha : IsNullMatrixSequence (DblIdx Y) cofinite a) :
    actQ Y w ω a = 0 := by
  refine vec_linearMap_ext Y w ω fun ξ ↦ ?_
  rw [actQ_mk, LinearMap.zero_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  show ((actSub Y w a ξ : massBounded Y w) : MatFam Y) ∈ massNull Y w ω
  rw [actSub_coe]
  exact applyFam_mem_massNull_of_isC0 Y w ω hw hω ha ξ.2

/-! ### The action of `B_ω` itself

`actQ` is defined on bounded sequences; the previous theorem says it kills the
`c₀` ideal, so it descends.  The descent is taken through a chosen lift rather
than through `Ideal.Quotient.lift`, because the corona is exposed behind an
opaque type synonym and every property below is then available without
unfolding it. -/

-- From here on the corona is formed, so the coordinate models must be
-- nonempty; see the note at the head of this section.
variable [∀ n, Nonempty (Y n)]

/-- A chosen bounded-sequence representative of a corona class. -/
def coronaLift (x : AdjointCorona Y) : BoundedMatrixSequence (DblIdx Y) :=
  Classical.choose (normMatrixCStarCoronaMk_surjective (DblIdx Y) x)

theorem coronaLift_spec (x : AdjointCorona Y) :
    normMatrixCStarCoronaMk (DblIdx Y) (coronaLift Y x) = x :=
  Classical.choose_spec (normMatrixCStarCoronaMk_surjective (DblIdx Y) x)

/-- **KT.03.**  The action of the norm ultraproduct `B_ω` on the
ultraproduct `K_ω`: `[A_n]_ω [ξ_n]_ω = [A_n ξ_n]_ω`. -/
def act (x : AdjointCorona Y) : Vec Y w ω →ₗ[ℂ] Vec Y w ω :=
  actQ Y w ω (coronaLift Y x)

/-- The action is computed by any representative, not only the chosen one. -/
theorem act_mk (hw : ∀ n, 0 ≤ w n) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (a : BoundedMatrixSequence (DblIdx Y)) :
    act Y w ω (normMatrixCStarCoronaMk (DblIdx Y) a) = actQ Y w ω a := by
  unfold act
  set b := coronaLift Y (normMatrixCStarCoronaMk (DblIdx Y) a) with hbdef
  have hspec : normMatrixCStarCoronaMk (DblIdx Y) b
      = normMatrixCStarCoronaMk (DblIdx Y) a :=
    coronaLift_spec Y (normMatrixCStarCoronaMk (DblIdx Y) a)
  have hzero : normMatrixCStarCoronaMk (DblIdx Y) (b - a) = 0 := by
    rw [map_sub, hspec, sub_self]
  have hc0 : IsNullMatrixSequence (DblIdx Y) cofinite (b - a) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (DblIdx Y) _).mp hzero
  have hz : actQ Y w ω b - actQ Y w ω a = 0 := by
    rw [← actQ_sub]
    exact actQ_eq_zero_of_isC0 Y w ω hw hω hc0
  exact sub_eq_zero.mp hz

/-- Scalars pass through the corona quotient map. -/
theorem coronaMk_smul (c : ℂ) (a : BoundedMatrixSequence (DblIdx Y)) :
    normMatrixCStarCoronaMk (DblIdx Y) (c • a)
      = c • normMatrixCStarCoronaMk (DblIdx Y) a := by
  have hq : ∀ b : BoundedMatrixSequence (DblIdx Y),
      normMatrixCStarCoronaQuotient (DblIdx Y) b
        = normMatrixCStarCoronaMk (DblIdx Y) b := fun _ ↦ rfl
  have h := map_smul (normMatrixCStarCoronaQuotient (DblIdx Y)) c a
  rw [hq, hq] at h
  exact h

section ActLaws

variable (hw : ∀ n, 0 ≤ w n) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

-- Every theorem of this section reaches for `hw` and `hω` only inside its
-- proof, through `act_mk`, so neither is auto-included by the elaborator.
include hw hω

theorem act_one : act Y w ω 1 = LinearMap.id := by
  have h1 : (1 : AdjointCorona Y) = normMatrixCStarCoronaMk (DblIdx Y) 1 :=
    (map_one (normMatrixCStarCoronaMk (DblIdx Y))).symm
  rw [h1, act_mk Y w ω hw hω, actQ_one]

theorem act_mul (x y : AdjointCorona Y) :
    act Y w ω (x * y) = (act Y w ω x).comp (act Y w ω y) := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) y
  rw [← map_mul, act_mk Y w ω hw hω, act_mk Y w ω hw hω,
    act_mk Y w ω hw hω, actQ_mul]

theorem act_add (x y : AdjointCorona Y) :
    act Y w ω (x + y) = act Y w ω x + act Y w ω y := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) y
  rw [← map_add, act_mk Y w ω hw hω, act_mk Y w ω hw hω,
    act_mk Y w ω hw hω, actQ_add]

theorem act_zero : act Y w ω 0 = 0 := by
  have h0 : (0 : AdjointCorona Y) = normMatrixCStarCoronaMk (DblIdx Y) 0 :=
    (map_zero (normMatrixCStarCoronaMk (DblIdx Y))).symm
  rw [h0, act_mk Y w ω hw hω, actQ_zero]

theorem act_sub (x y : AdjointCorona Y) :
    act Y w ω (x - y) = act Y w ω x - act Y w ω y := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) y
  rw [← map_sub, act_mk Y w ω hw hω, act_mk Y w ω hw hω,
    act_mk Y w ω hw hω, actQ_sub]

/-- **The action is `ℂ`-linear in the algebra argument.**  This is the field
of the construction that the Kazhdan projection step consumes: it is what
lets the averaged operator `h = |S|⁻¹ Σ π(ι s')` be evaluated on a vector. -/
theorem act_smul (c : ℂ) (x : AdjointCorona Y) :
    act Y w ω (c • x) = c • act Y w ω x := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (DblIdx Y) x
  rw [← coronaMk_smul, act_mk Y w ω hw hω, act_mk Y w ω hw hω, actQ_smul]

theorem act_finset_sum {ι : Type*} (t : Finset ι) (f : ι → AdjointCorona Y)
    (ζ : Vec Y w ω) :
    act Y w ω (∑ i ∈ t, f i) ζ = ∑ i ∈ t, act Y w ω (f i) ζ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, act_zero Y w ω hw hω,
        LinearMap.zero_apply]
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        act_add Y w ω hw hω, LinearMap.add_apply, ih]

end ActLaws

/-! ## KT.01 and KT.05: the adjoint representation `π(g) = [Ad U_n(g)]_ω` -/

section Representation

variable {H : Type*} [Group H] (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)

/-- **KT.01.**  The unitary `Ad U_n(g)` of `K_n`, as a matrix on the doubled
index.  This is the manuscript's "finite-stage form of the `π ⊗ π̄`
construction". -/
def adjUnitary (g : H) (n : ℕ) : Matrix.unitaryGroup (DblFam Y n) ℂ :=
  ⟨conjDouble (U n g : Matrix (Y n) (Y n) ℂ),
    conjDouble_mem_unitaryGroup (U n g).2⟩

omit [∀ n, Nonempty (Y n)] [Group H] in
@[simp] theorem adjUnitary_coe (g : H) (n : ℕ) :
    ((adjUnitary Y U g n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
        Matrix (DblFam Y n) (DblFam Y n) ℂ)
      = conjDouble (U n g : Matrix (Y n) (Y n) ℂ) := rfl

omit [∀ n, Nonempty (Y n)] in
/-- **KT.01.**  Operator-norm asymptotic multiplicativity passes to the
adjoint model with no dimension loss, because the conjugate double is
`2`-Lipschitz on the unitary group. -/
theorem adjUnitary_asymptoticallyMultiplicative
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (g h : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖((adjUnitary Y U (g * h) n :
            Matrix.unitaryGroup (DblFam Y n) ℂ) :
            Matrix (DblFam Y n) (DblFam Y n) ℂ) -
          ((adjUnitary Y U g n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
            Matrix (DblFam Y n) (DblFam Y n) ℂ) *
            ((adjUnitary Y U h n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
              Matrix (DblFam Y n) (DblFam Y n) ℂ)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := hU g h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hd := l2_opNorm_conjDouble_defect_le (U n (g * h)).2 (U n g).2
    (U n h).2 (hN n hn)
  have htwo : (2 : ℝ) * (ε / 2) = ε := by ring
  rw [htwo] at hd
  exact hd

/-- **KT.05, the analytic input.**  The multiplicative defect of the adjoint
model tends to zero in operator norm, hence lies in the `c₀` ideal, hence is
invisible in the corona. -/
theorem adjCorona_mul
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)
    (g h : H) :
    unitarySequenceToCorona (DblFam Y) (fun n ↦ adjUnitary Y U (g * h) n) =
      unitarySequenceToCorona (DblFam Y)
        (fun n ↦ adjUnitary Y U g n * adjUnitary Y U h n) := by
  have hzero : normMatrixCStarCoronaMk (DblIdx Y)
      (unitarySequenceBounded (DblFam Y) (fun n ↦ adjUnitary Y U (g * h) n) -
        unitarySequenceBounded (DblFam Y)
          (fun n ↦ adjUnitary Y U g n * adjUnitary Y U h n)) = 0 := by
    rw [normMatrixCStarCoronaMk_eq_zero_iff]
    show Tendsto (fun n ↦
        ‖(unitarySequenceBounded (DblFam Y)
              (fun m ↦ adjUnitary Y U (g * h) m) -
            unitarySequenceBounded (DblFam Y)
              (fun m ↦ adjUnitary Y U g m * adjUnitary Y U h m)) n‖)
      Filter.cofinite (nhds 0)
    rw [Nat.cofinite_eq_atTop, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      adjUnitary_asymptoticallyMultiplicative Y U hU g h (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Real.dist_eq, sub_zero, abs_norm]
    have hcoord :
        (unitarySequenceBounded (DblFam Y)
              (fun m ↦ adjUnitary Y U (g * h) m) -
            unitarySequenceBounded (DblFam Y)
              (fun m ↦ adjUnitary Y U g m * adjUnitary Y U h m)) n =
          ((adjUnitary Y U (g * h) n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
              Matrix (DblFam Y n) (DblFam Y n) ℂ) -
            ((adjUnitary Y U g n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
                Matrix (DblFam Y n) (DblFam Y n) ℂ) *
              ((adjUnitary Y U h n : Matrix.unitaryGroup (DblFam Y n) ℂ) :
                Matrix (DblFam Y n) (DblFam Y n) ℂ) := rfl
    rw [hcoord]
    exact lt_of_le_of_lt (hN n hn) (by linarith)
  rw [map_sub, sub_eq_zero] at hzero
  exact Subtype.ext hzero

/-- **KT.05.**  `π : H → U(B_ω)`, `π(g) = [Ad U_n(g)]_ω`, is a genuine group
homomorphism: the asymptotic multiplicativity of `(U_n)` becomes exact in the
quotient. -/
def piUnitary
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε) :
    H →* unitary (AdjointCorona Y) :=
  MonoidHom.mk'
    (fun g ↦ unitarySequenceToCorona (DblFam Y) (fun n ↦ adjUnitary Y U g n))
    (fun g h ↦ by
      show unitarySequenceToCorona (DblFam Y)
          (fun n ↦ adjUnitary Y U (g * h) n) =
        unitarySequenceToCorona (DblFam Y) (fun n ↦ adjUnitary Y U g n) *
          unitarySequenceToCorona (DblFam Y) (fun n ↦ adjUnitary Y U h n)
      rw [adjCorona_mul Y U hU g h]
      exact map_mul (unitarySequenceToCorona (DblFam Y))
        (fun n ↦ adjUnitary Y U g n) (fun n ↦ adjUnitary Y U h n))

variable (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
  ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
    (U n g : Matrix (Y n) (Y n) ℂ) * (U n h : Matrix (Y n) (Y n) ℂ)‖ ≤ ε)

/-- `π` read inside the algebra rather than in its unitary group. -/
def piHom : H →* AdjointCorona Y :=
  (unitary (AdjointCorona Y)).subtype.comp (piUnitary Y U hU)

/-- The bounded-sequence representative of `π g`. -/
def piSeq (g : H) : BoundedMatrixSequence (DblIdx Y) :=
  unitarySequenceBounded (DblFam Y) (fun n ↦ adjUnitary Y U g n)

@[simp] theorem piHom_eq_mk (g : H) :
    piHom Y U hU g = normMatrixCStarCoronaMk (DblIdx Y) (piSeq Y U g) := rfl

omit [Group H] in
@[simp] theorem piSeq_apply (g : H) (n : ℕ) :
    piSeq Y U g n = conjDouble (U n g : Matrix (Y n) (Y n) ℂ) := rfl

/-- **KT.05.**  `π` is a star homomorphism: `π(g)* = π(g⁻¹)`. -/
theorem piHom_star (g : H) : star (piHom Y U hU g) = piHom Y U hU g⁻¹ :=
  AbstractSpectralGap.star_unitary_coe (piUnitary Y U hU) g

theorem star_piHom_eq_mk (g : H) :
    star (piHom Y U hU g)
      = normMatrixCStarCoronaMk (DblIdx Y) (star (piSeq Y U g)) := by
  rw [piHom_eq_mk]
  exact normMatrixCStarCorona_star_mk (DblIdx Y) (piSeq Y U g)

/-! ### The representation on coordinates -/

omit [Group H] in
theorem applyFam_piSeq (g : H) (ξ : MatFam Y) :
    applyFam Y (piSeq Y U g) ξ =
      fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ := by
  funext n
  show rowMat (piSeq Y U g n *ᵥ rowVec (ξ n)) = _
  rw [piSeq_apply]
  exact rowMat_conjDouble_mulVec (Y n) _ (ξ n)

omit [Group H] in
theorem star_piSeq_apply (g : H) (n : ℕ) :
    (star (piSeq Y U g)) n
      = conjDouble ((U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
  rw [lp.star_apply, conjDouble_conjTranspose]
  show star (conjDouble (U n g : Matrix (Y n) (Y n) ℂ))
      = (conjDouble (U n g : Matrix (Y n) (Y n) ℂ))ᴴ
  exact Matrix.star_eq_conjTranspose _

omit [Group H] in
theorem applyFam_star_piSeq (g : H) (ξ : MatFam Y) :
    applyFam Y (star (piSeq Y U g)) ξ =
      fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ) := by
  funext n
  show rowMat ((star (piSeq Y U g)) n *ᵥ rowVec (ξ n)) = _
  rw [star_piSeq_apply, rowMat_conjDouble_mulVec (Y n) _ (ξ n),
    Matrix.conjTranspose_conjTranspose]

/-! ### The representation on classes -/

/-- **KT.01 and KT.03.**  `π g` acts on ultraproduct classes by the
ultraproduct of the adjoint actions `Ad U_n(g) ξ = U_n(g) ξ U_n(g)*`.  No mass
bound is needed: conjugation by a unitary preserves the Frobenius mass
exactly, so it preserves the mass-bounded families and their complement
alike. -/
theorem act_pi_cls (hw : ∀ n, 0 ≤ w n)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (g : H) (ξ : MatFam Y) :
    act Y w ω (piHom Y U hU g) (cls Y w ω ξ) =
      cls Y w ω (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
  have hmass : ∀ n, matMass ((U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) = matMass (ξ n) :=
    fun n ↦ kt_01_matMass_adjoint (U n g).2 (ξ n)
  rw [piHom_eq_mk, act_mk Y w ω hw hω]
  by_cases hb : ξ ∈ massBounded Y w
  · obtain ⟨C, hC⟩ := hb
    have hb' : ξ ∈ massBounded Y w := ⟨C, hC⟩
    have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) ∈ massBounded Y w :=
      ⟨C, fun n ↦ by rw [hmass n]; exact hC n⟩
    rw [cls_of_mem Y w ω hb', actQ_mk, cls_of_mem Y w ω hcb]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (applyFam_piSeq Y U g ξ))
  · have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) ∉ massBounded Y w := by
      rintro ⟨C, hC⟩
      exact hb ⟨C, fun n ↦ by rw [← hmass n]; exact hC n⟩
    rw [cls_of_not_mem Y w ω hb, cls_of_not_mem Y w ω hcb, map_zero]

/-- **KT.01 and KT.03, adjoint form.**  `(π g)*` acts by the reverse
conjugation `ξ ↦ U_n(g)* ξ U_n(g)`, which is what the second conclusion of
`thm:transport-variants`(1) needs. -/
theorem act_star_pi_cls (hw : ∀ n, 0 ≤ w n)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (g : H) (ξ : MatFam Y) :
    act Y w ω (star (piHom Y U hU g)) (cls Y w ω ξ) =
      cls Y w ω (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) := by
  have hmass : ∀ n, matMass ((U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)) = matMass (ξ n) :=
    fun n ↦ kt_01_matMass_coadjoint (U n g).2 (ξ n)
  rw [star_piHom_eq_mk, act_mk Y w ω hw hω]
  by_cases hb : ξ ∈ massBounded Y w
  · obtain ⟨C, hC⟩ := hb
    have hb' : ξ ∈ massBounded Y w := ⟨C, hC⟩
    have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) ∈ massBounded Y w :=
      ⟨C, fun n ↦ by rw [hmass n]; exact hC n⟩
    rw [cls_of_mem Y w ω hb', actQ_mk, cls_of_mem Y w ω hcb]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (applyFam_star_piSeq Y U g ξ))
  · have hcb : (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)) ∉ massBounded Y w := by
      rintro ⟨C, hC⟩
      exact hb ⟨C, fun n ↦ by rw [← hmass n]; exact hC n⟩
    rw [cls_of_not_mem Y w ω hb, cls_of_not_mem Y w ω hcb, map_zero]

end Representation

end Action

end

end UltraproductModelConstruction
end GroupApproximation
