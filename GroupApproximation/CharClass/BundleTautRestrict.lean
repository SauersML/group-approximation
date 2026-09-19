import GroupApproximation.CharClass.BundleCoordEmbed
import GroupApproximation.CharClass.BundleInvariance

/-!
# Complex vector bundles in the projection model, XVII: the tautological line
along the hyperplane inclusion

`projIncl p : P(p) → P(p ⊕ 1)` is the hyperplane at infinity, and it carries the
tautological line to the tautological line.  The comparison is not an identity,
because `tautLine p` is indexed by `ι` while `tautLine p.plusOne` is indexed by
`ι ⊕ Unit`; but a `BundleIso` is rectangular, so the block padding is exactly
what it accommodates.

The implementer is the point's own matrix followed by the block row: for
`z = (x, r)` in `P(p)`,

    a z = r * (inlMat ι)ᴴ ,     aᴴ a = inclMat r ,     a aᴴ = r ,

using only that `r` is a self-adjoint idempotent and that `inlMat` is an
isometry.  `projIncl` pads by `inclMat`, so `aᴴ a` really is the pullback.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### The block column -/

/-- The block column `[1; 0] : Matrix (ι ⊕ Unit) ι ℂ`, the coordinate inclusion
of `ℂ^ι` as the first summand. -/
def inlMat (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix (ι ⊕ Unit) ι ℂ :=
  coordIncl Sum.inl

theorem inlMat_isometry (ι : Type) [Fintype ι] [DecidableEq ι] :
    (inlMat ι)ᴴ * inlMat ι = (1 : Matrix ι ι ℂ) :=
  coordIncl_isometry Sum.inl_injective

theorem inclMat_apply_inl_inr {ι : Type} [Fintype ι] (q : Matrix ι ι ℂ) (i : ι) (u : Unit) :
    inclMat q (Sum.inl i) (Sum.inr u) = 0 := rfl

theorem inclMat_apply_inr_inl {ι : Type} [Fintype ι] (q : Matrix ι ι ℂ) (u : Unit) (j : ι) :
    inclMat q (Sum.inr u) (Sum.inl j) = 0 := rfl

/-- **Conjugating by the block column is the block embedding.** -/
theorem inlMat_conj (ι : Type) [Fintype ι] [DecidableEq ι] (q : Matrix ι ι ℂ) :
    inlMat ι * q * (inlMat ι)ᴴ = inclMat q := by
  ext s t
  cases s with
  | inl i =>
      cases t with
      | inl j =>
          rw [inclMat_apply_inl_inl]
          exact coordIncl_conj_apply Sum.inl_injective q i j
      | inr u =>
          rw [inclMat_apply_inl_inr]
          exact coordIncl_conj_apply_col (fun j => Sum.inr_ne_inl) q _
  | inr u =>
      cases t with
      | inl j =>
          rw [inclMat_apply_inr_inl]
          exact coordIncl_conj_apply_row (fun i => Sum.inr_ne_inl) q _
      | inr u' =>
          rw [inclMat_apply_inr_inr]
          exact coordIncl_conj_apply_row (fun i => Sum.inr_ne_inl) q _

/-! ### The tautological line restricts to the tautological line -/

section Restrict

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The hyperplane inclusion carries the tautological line to the tautological
line.**  Pulling back the tautological line of `P(p ⊕ 1)` along `projIncl p`
gives the tautological line of `P(p)`, with the block padding that the two index
types force absorbed into the rectangular implementer. -/
def tautRestrictIso (p : Bundle X ι) :
    BundleIso (comap (projIncl p) (tautLine p.plusOne)) (tautLine p) where
  hom z := (z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ
  continuous_hom :=
    (continuous_snd.comp continuous_subtype_val).matrix_mul continuous_const
  conjTranspose_mul z := by
    have hrH : ((z : X × Matrix ι ι ℂ).2)ᴴ = (z : X × Matrix ι ι ℂ).2 := z.2.1
    have hrr : (z : X × Matrix ι ι ℂ).2 * (z : X × Matrix ι ι ℂ).2
        = (z : X × Matrix ι ι ℂ).2 := z.2.2.1
    show ((z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ)ᴴ * ((z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ)
      = inclMat (z : X × Matrix ι ι ℂ).2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hrH]
    calc inlMat ι * (z : X × Matrix ι ι ℂ).2
            * ((z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ)
        = inlMat ι * ((z : X × Matrix ι ι ℂ).2 * (z : X × Matrix ι ι ℂ).2)
            * (inlMat ι)ᴴ := by simp only [Matrix.mul_assoc]
      _ = inlMat ι * (z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ := by rw [hrr]
      _ = inclMat (z : X × Matrix ι ι ℂ).2 := inlMat_conj ι _
  mul_conjTranspose z := by
    have hrH : ((z : X × Matrix ι ι ℂ).2)ᴴ = (z : X × Matrix ι ι ℂ).2 := z.2.1
    have hrr : (z : X × Matrix ι ι ℂ).2 * (z : X × Matrix ι ι ℂ).2
        = (z : X × Matrix ι ι ℂ).2 := z.2.2.1
    show ((z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ)
        * ((z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ)ᴴ
      = (z : X × Matrix ι ι ℂ).2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hrH]
    calc (z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ
            * (inlMat ι * (z : X × Matrix ι ι ℂ).2)
        = (z : X × Matrix ι ι ℂ).2 * ((inlMat ι)ᴴ * inlMat ι)
            * (z : X × Matrix ι ι ℂ).2 := by simp only [Matrix.mul_assoc]
      _ = (z : X × Matrix ι ι ℂ).2 * 1 * (z : X × Matrix ι ι ℂ).2 := by
          rw [inlMat_isometry]
      _ = (z : X × Matrix ι ι ℂ).2 := by rw [Matrix.mul_one, hrr]

theorem tautRestrictIso_hom (p : Bundle X ι) (z : Proj p) :
    (tautRestrictIso p).hom z = (z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ := rfl

end Restrict

end Bundle

end CharClass
end GroupApproximation
