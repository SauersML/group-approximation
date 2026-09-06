import GroupApproximation.CharClass.BundleOneStep

/-!
# Complex vector bundles in the projection model, XXII: rank one, and reindexing

Two things a consumer working in `ℂP^d` needs from this lane.

**The projectivisation of a rank-one bundle is the base.**  Each fibre is a
single point, and in this model that is sharp: a point of `P(p)` is a
subprojection of `p` of trace one, so when `p` itself has trace one the two are
equal, by the trace argument.

**Reindexing along an equivalence of index types.**  `plusOne` produces `ι ⊕ Unit`
while `classifyOne` and an Euler class want `Fin (d+1)`.  `reindex` conjugates by
the coordinate permutation, so entries stay definitional and no matrix
arithmetic appears at the seam.  It comes with a `BundleIso`, which is what makes
every space and the tautological line transport along it through the existing
`projHomeo` and `tautIso` rather than through anything new.

Composed with `sumUnitEquiv`, `reindex` puts `p.plusOne` at `Fin (d + 2)`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### The projectivisation of a rank-one bundle -/

section RankOne

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **A point of `P(p)` over a rank-one `p` is `p` itself.**  It is a
subprojection of `p` of the same trace, and a projection of trace zero is
zero. -/
theorem eq_of_mem_projSet_of_trace_one {p : Bundle X ι} (hp : ∀ x, (p x).trace = 1)
    (z : Proj p) :
    (z : X × Matrix ι ι ℂ).2 = p (z : X × Matrix ι ι ℂ).1 := by
  have hsub : IsStarProjection
      (p (z : X × Matrix ι ι ℂ).1 - (z : X × Matrix ι ι ℂ).2) :=
    isStarProjection_sub (p.isStarProjection _) (isStarProjection_of_mem_projSet z.2)
      z.2.2.2.2 (absorb_right_of_mem_projSet z.2)
  have htr : (p (z : X × Matrix ι ι ℂ).1 - (z : X × Matrix ι ι ℂ).2).trace = 0 := by
    rw [Matrix.trace_sub, hp, trace_of_mem_projSet z.2, sub_self]
  exact (sub_eq_zero.mp (proj_eq_zero_of_trace_eq_zero hsub htr)).symm

/-- **The projectivisation of a rank-one bundle is the base**, over the base. -/
def projRankOneHomeo (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) : Proj p ≃ₜ X where
  toFun z := (z : X × Matrix ι ι ℂ).1
  invFun x := ⟨(x, p x), p.conjTranspose_eq x, p.mul_self x, hp x, p.mul_self x⟩
  left_inv z := Subtype.ext (Prod.ext rfl (eq_of_mem_projSet_of_trace_one hp z).symm)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk p.continuous).subtype_mk _

theorem projRankOneHomeo_over_base (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (z : Proj p) : projRankOneHomeo p hp z = projPi p z := rfl

end RankOne

/-! ### Reindexing along an equivalence of index types -/

section Reindex

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

/-- **Reindexing a bundle along an equivalence of index types**, by conjugation
with the coordinate permutation. -/
def reindex (e : ι ≃ κ) (p : Bundle X ι) : Bundle X κ where
  toFun x := coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ
  continuous_toFun :=
    (continuous_const.matrix_mul p.continuous).matrix_mul continuous_const
  isStarProjection_toFun x := by
    rw [isStarProjection_matrix_iff]
    have hu : (coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ) = 1 :=
      coordIncl_isometry e.injective
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hpH]
      simp only [Matrix.mul_assoc]
    · calc coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ
              * (coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ)
          = coordIncl (e : ι → κ) * p x
              * ((coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ))
              * (p x * (coordIncl (e : ι → κ))ᴴ) := by simp only [Matrix.mul_assoc]
        _ = coordIncl (e : ι → κ) * p x * (1 : Matrix ι ι ℂ)
              * (p x * (coordIncl (e : ι → κ))ᴴ) := by rw [hu]
        _ = coordIncl (e : ι → κ) * p x * (p x * (coordIncl (e : ι → κ))ᴴ) := by
              rw [Matrix.mul_one]
        _ = coordIncl (e : ι → κ) * (p x * p x) * (coordIncl (e : ι → κ))ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ := by rw [p.mul_self]

theorem reindex_apply (e : ι ≃ κ) (p : Bundle X ι) (x : X) :
    reindex e p x = coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ := rfl

/-- **The entries are those of `p`, relabelled.** -/
theorem reindex_apply_entry (e : ι ≃ κ) (p : Bundle X ι) (x : X) (i j : ι) :
    reindex e p x (e i) (e j) = p x i j :=
  coordIncl_conj_apply e.injective (p x) i j

theorem trace_reindex (e : ι ≃ κ) (p : Bundle X ι) (x : X) :
    (reindex e p x).trace = (p x).trace := by
  have hu : (coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ) = 1 :=
    coordIncl_isometry e.injective
  show (coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ).trace = (p x).trace
  rw [Matrix.trace_mul_comm]
  calc ((coordIncl (e : ι → κ))ᴴ * (coordIncl (e : ι → κ) * p x)).trace
      = (((coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ)) * p x).trace := by
        simp only [Matrix.mul_assoc]
    _ = (p x).trace := by rw [hu, Matrix.one_mul]

/-- **Reindexing is an isomorphism.**  So every space attached to `p`, and the
tautological line, transport along it through `projHomeo` and `tautIso`; no new
naturality statement is needed. -/
def reindexIso (e : ι ≃ κ) (p : Bundle X ι) : BundleIso p (reindex e p) where
  hom x := coordIncl (e : ι → κ) * p x
  continuous_hom := continuous_const.matrix_mul p.continuous
  conjTranspose_mul x := by
    have hu : (coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ) = 1 :=
      coordIncl_isometry e.injective
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    rw [Matrix.conjTranspose_mul, hpH]
    calc p x * (coordIncl (e : ι → κ))ᴴ * (coordIncl (e : ι → κ) * p x)
        = p x * ((coordIncl (e : ι → κ))ᴴ * coordIncl (e : ι → κ)) * p x := by
          simp only [Matrix.mul_assoc]
      _ = p x * 1 * p x := by rw [hu]
      _ = p x := by rw [Matrix.mul_one, p.mul_self]
  mul_conjTranspose x := by
    have hpH : (p x)ᴴ = p x := p.conjTranspose_eq x
    rw [Matrix.conjTranspose_mul, hpH]
    show coordIncl (e : ι → κ) * p x * (p x * (coordIncl (e : ι → κ))ᴴ)
      = coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ
    calc coordIncl (e : ι → κ) * p x * (p x * (coordIncl (e : ι → κ))ᴴ)
        = coordIncl (e : ι → κ) * (p x * p x) * (coordIncl (e : ι → κ))ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = coordIncl (e : ι → κ) * p x * (coordIncl (e : ι → κ))ᴴ := by rw [p.mul_self]

end Reindex

end Bundle

end CharClass
end GroupApproximation
