import GroupApproximation.Algebra.FinitaryLinearBinaryPower
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Finite matrix support is stronger than finite rank

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1131--1133):

> Let `GL_fs(V^n)` be the group of automorphisms `g` of `V^n` such that `g - I`
> has finite matrix support in this basis, a condition stronger than finite rank
> of `g - I`.

Both halves of "stronger":

* every finitary automorphism has `g - I` of finite rank: its range lies in the
  finite-dimensional block span (`finiteDimensional_range_sub_id_of_mem_finitary`);
* the transvection `x ↦ x + (Σ_{j ≥ 1} coefficient of b_{(0,j)} in x) • b_{(0,0)}`
  of `V^n` has `g - I` of rank one but infinite matrix support, so the converse
  fails (`binaryWideTransvection_not_mem_binaryGLfs`).
-/

namespace GroupApproximation
namespace FinitaryLinear

universe u v w

section General

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M] {β : Type w}
  (B : Module.Basis β F M)

/-- For a finitary automorphism, `g - I` has finite rank. -/
theorem finiteDimensional_range_sub_id_of_mem_finitary {g : M ≃ₗ[F] M} (hg : g ∈ finitary B) :
    FiniteDimensional F (LinearMap.range ((g : M →ₗ[F] M) - LinearMap.id)) := by
  obtain ⟨T, hT⟩ := (mem_finitary B).mp hg
  have hle : LinearMap.range ((g : M →ₗ[F] M) - LinearMap.id) ≤ blockSpan B T := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span F (Set.range B) := by
      rw [B.span_eq]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ ↦
      ((g : M →ₗ[F] M) - LinearMap.id) x ∈ blockSpan B T) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, rfl⟩
      by_cases hb : b ∈ T
      · simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
        exact Submodule.sub_mem _ (hT.maps _ (basis_mem_blockSpan B hb)) (basis_mem_blockSpan B hb)
      · simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hT.fix b hb,
          sub_self]
        exact Submodule.zero_mem _
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  exact Submodule.finiteDimensional_of_le hle

end General

section Binary

variable (n : ℕ) [NeZero n]

/-- The functional `x ↦ Σ_{j ≥ 1} (coefficient of X^j in coordinate 0 of x)`,
i.e. evaluation at `1` minus the constant coefficient. -/
noncomputable def wideFunctional : BinaryPower n →ₗ[ZMod 2] ZMod 2 :=
  (Polynomial.leval (1 : ZMod 2) - Polynomial.lcoeff (ZMod 2) 0) ∘ₗ
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n ↦ BinarySpace) 0

/-- The basis vector `b_{(0,0)}`. -/
noncomputable def firstVector : BinaryPower n := Pi.single 0 1

theorem wideFunctional_firstVector : wideFunctional n (firstVector n) = 0 := by
  simp [wideFunctional, firstVector, Polynomial.leval, sub_self]

/-- The rank-one map `x ↦ x + ψ(x) b_{(0,0)}`. -/
noncomputable def wideLin : BinaryPower n →ₗ[ZMod 2] BinaryPower n :=
  LinearMap.id + (wideFunctional n).smulRight (firstVector n)

theorem wideLin_comp_self : wideLin n ∘ₗ wideLin n = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  have hc : ∀ c : ZMod 2, c + c = 0 := by decide
  simp only [wideLin, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, map_add, map_smul, wideFunctional_firstVector, smul_eq_mul,
    mul_zero, add_zero]
  rw [add_assoc, ← add_smul, hc, zero_smul, add_zero]

/-- **A transvection with infinite matrix support.** -/
noncomputable def binaryWideTransvection : BinaryPower n ≃ₗ[ZMod 2] BinaryPower n :=
  LinearEquiv.ofLinear (wideLin n) (wideLin n) (wideLin_comp_self n) (wideLin_comp_self n)

theorem binaryWideTransvection_sub_id :
    ((binaryWideTransvection n : BinaryPower n →ₗ[ZMod 2] BinaryPower n) - LinearMap.id) =
      (wideFunctional n).smulRight (firstVector n) := by
  refine LinearMap.ext fun x ↦ ?_
  simp [binaryWideTransvection, wideLin]

/-- `g - I` has rank at most one. -/
theorem finiteDimensional_range_binaryWideTransvection :
    FiniteDimensional (ZMod 2)
      (LinearMap.range ((binaryWideTransvection n : BinaryPower n →ₗ[ZMod 2] BinaryPower n) -
        LinearMap.id)) := by
  rw [binaryWideTransvection_sub_id]
  have hle : LinearMap.range ((wideFunctional n).smulRight (firstVector n)) ≤
      Submodule.span (ZMod 2) {firstVector n} := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  haveI : FiniteDimensional (ZMod 2) (Submodule.span (ZMod 2) {firstVector n}) :=
    FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_singleton _)
  exact Submodule.finiteDimensional_of_le hle

theorem binaryPowerBasis_apply_zero (j : ℕ) :
    binaryPowerBasis n ⟨0, j⟩ = Pi.single 0 (Polynomial.monomial j 1) := by
  simp [binaryPowerBasis, Polynomial.coe_basisMonomials]

/-- The entries `((0,0),(0,j))`, `j ≥ 1`, of `g - I` are nonzero. -/
theorem wideTransvection_entry (j : ℕ) :
    (binaryPowerBasis n).repr
      (((binaryWideTransvection n : BinaryPower n →ₗ[ZMod 2] BinaryPower n) - LinearMap.id)
        (binaryPowerBasis n ⟨0, j + 1⟩)) ⟨0, 0⟩ = 1 := by
  rw [binaryWideTransvection_sub_id, LinearMap.smulRight_apply, map_smul,
    binaryPowerBasis_apply_zero]
  have hfirst : firstVector n = binaryPowerBasis n ⟨0, 0⟩ := by
    rw [binaryPowerBasis_apply_zero, firstVector, Polynomial.monomial_zero_one]
  rw [hfirst, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one]
  simp [wideFunctional, Polynomial.leval, Polynomial.eval_monomial, Polynomial.coeff_monomial]

/-- **The converse fails**: this transvection is not in `GL_fs(V^n)`. -/
theorem binaryWideTransvection_not_mem_binaryGLfs :
    binaryWideTransvection n ∉ binaryGLfs n := by
  rw [mem_binaryGLfs_iff]
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ ↦ ((⟨0, 0⟩ : Σ _ : Fin n, ℕ), (⟨0, j + 1⟩ : Σ _ : Fin n, ℕ)))
    (fun a b h ↦ by simpa using h) fun j ↦ ?_
  show (binaryPowerBasis n).repr
      (((binaryWideTransvection n : BinaryPower n →ₗ[ZMod 2] BinaryPower n) - LinearMap.id)
        (binaryPowerBasis n ⟨0, j + 1⟩)) ⟨0, 0⟩ ≠ 0
  rw [wideTransvection_entry]
  exact one_ne_zero

end Binary

/-- **Printed (tex 1131--1133).**  Finite matrix support of `g - I` is a condition
stronger than finite rank of `g - I`: it implies it, and not conversely. -/
theorem manuscriptSentence_finiteSupportStrongerThanFiniteRank :
    ∀ n : ℕ, 0 < n →
      (∀ g ∈ binaryGLfs n,
        FiniteDimensional (ZMod 2)
          (LinearMap.range ((g : BinaryPower n →ₗ[ZMod 2] BinaryPower n) - LinearMap.id))) ∧
      ∃ g : BinaryPower n ≃ₗ[ZMod 2] BinaryPower n,
        FiniteDimensional (ZMod 2)
          (LinearMap.range ((g : BinaryPower n →ₗ[ZMod 2] BinaryPower n) - LinearMap.id)) ∧
        g ∉ binaryGLfs n := by
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨fun g hg ↦ finiteDimensional_range_sub_id_of_mem_finitary _ hg,
    binaryWideTransvection n, finiteDimensional_range_binaryWideTransvection n,
    binaryWideTransvection_not_mem_binaryGLfs n⟩

end FinitaryLinear
end GroupApproximation

#audit_closed_axioms GroupApproximation.FinitaryLinear.manuscriptSentence_finiteSupportStrongerThanFiniteRank
