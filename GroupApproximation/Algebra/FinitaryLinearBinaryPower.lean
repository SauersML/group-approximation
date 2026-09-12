import GroupApproximation.Algebra.FinitaryLinearBinarySLUnion
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Denumerable

/-!
# The printed `GL_fs(V^n)` and its identification with `⋃_N SL_N(F_2)`

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1131--1145):

> Let `GL_fs(V^n)` be the group of automorphisms `g` of `V^n` such that `g - I`
> has finite matrix support in this basis … `≅ ⋃_N SL_N(F_2)`.

`V^n` is `Fin n → F_2[X]` with the standard basis `b_{(i,j)} = X^j` in coordinate
`i` (`Pi.basis`), and `GL_fs(V^n)` is the finitary group of that basis
(`binaryGLfs`); its membership condition is literally the printed one
(`mem_binaryGLfs_iff`).  Conjugation along a linear equivalence carrying one
basis to another by an index bijection carries finitary groups onto each other
(`conjAut_map_finitary`), and a bijection `Σ (i : Fin n), ℕ ≃ ℕ` (`n ≥ 1`) gives
`GL_fs(V^n) ≃* ⋃_N SL_N(F_2)` (`binaryGLfsEquivSLUnion`).
-/

namespace GroupApproximation
namespace FinitaryLinear

universe u v v' w w'

/-! ## Transport of finitary groups along bases -/

section Transport

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M] {β : Type w}
  {M' : Type v'} [AddCommGroup M'] [Module F M'] {β' : Type w'}

/-- Conjugation of automorphisms along a linear equivalence. -/
def conjAut (e : M ≃ₗ[F] M') : (M ≃ₗ[F] M) ≃* (M' ≃ₗ[F] M') where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by
    ext x
    simp
  right_inv g := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

@[simp] theorem conjAut_apply (e : M ≃ₗ[F] M') (g : M ≃ₗ[F] M) (x : M') :
    conjAut e g x = e (g (e.symm x)) := rfl

variable (B : Module.Basis β F M) (B' : Module.Basis β' F M') (σ : β ≃ β')

theorem map_blockSpan_le {e : M ≃ₗ[F] M'} (he : ∀ b, e (B b) = B' (σ b)) (T : Finset β) :
    (blockSpan B T).map (e : M →ₗ[F] M') ≤ blockSpan B' (T.map σ.toEmbedding) := by
  rw [blockSpan, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  exact ⟨σ b, by simpa using hb, (he b).symm⟩

/-- Conjugation along a basis-to-basis equivalence carries finitary automorphisms
to finitary automorphisms. -/
theorem conjAut_mem_finitary {e : M ≃ₗ[F] M'} (he : ∀ b, e (B b) = B' (σ b))
    {g : M ≃ₗ[F] M} (hg : g ∈ finitary B) : conjAut e g ∈ finitary B' := by
  classical
  obtain ⟨T, hT⟩ := (mem_finitary B).mp hg
  have hsymm : ∀ b', e.symm (B' b') = B (σ.symm b') := fun b' ↦ by
    rw [LinearEquiv.symm_apply_eq, he, Equiv.apply_symm_apply]
  refine (mem_finitary B').mpr ⟨T.map σ.toEmbedding, IsSupportedOn.of_basis (fun b' hb' ↦ ?_)
    fun b' hb' ↦ ?_⟩
  · have hnot : σ.symm b' ∉ T := fun h ↦ hb' (by simpa [Finset.mem_map_equiv] using h)
    rw [conjAut_apply, hsymm, hT.fix _ hnot, he, Equiv.apply_symm_apply]
  · have hin : σ.symm b' ∈ T := by simpa [Finset.mem_map_equiv] using hb'
    rw [conjAut_apply, hsymm]
    exact map_blockSpan_le B B' σ he T ⟨_, hT.maps _ (basis_mem_blockSpan B hin), rfl⟩

/-- **Transport of finitary groups.** -/
theorem conjAut_map_finitary {e : M ≃ₗ[F] M'} (he : ∀ b, e (B b) = B' (σ b)) :
    (finitary B).map (conjAut e).toMonoidHom = finitary B' := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact conjAut_mem_finitary B B' σ he hg
  · have he' : ∀ b', e.symm (B' b') = B (σ.symm b') := fun b' ↦ by
      rw [LinearEquiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    refine ⟨conjAut e.symm g, conjAut_mem_finitary B' B σ.symm he' hg, ?_⟩
    ext x
    simp

/-- The finitary groups of two bases related by an index bijection are
isomorphic. -/
noncomputable def finitaryEquivOfBasis {e : M ≃ₗ[F] M'} (he : ∀ b, e (B b) = B' (σ b)) :
    finitary B ≃* finitary B' :=
  ((conjAut e).subgroupMap (finitary B)).trans
    (MulEquiv.subgroupCongr (conjAut_map_finitary B B' σ he))

end Transport

/-! ## The printed `V^n` -/

/-- The printed `V^n`. -/
abbrev BinaryPower (n : ℕ) : Type := Fin n → BinarySpace

/-- The standard basis `b_{(i,j)} = X^j` in coordinate `i` of `V^n`. -/
noncomputable abbrev binaryPowerBasis (n : ℕ) :
    Module.Basis (Σ _ : Fin n, ℕ) (ZMod 2) (BinaryPower n) :=
  Pi.basis fun _ ↦ binaryBasis

/-- **The printed `GL_fs(V^n)`.** -/
noncomputable def binaryGLfs (n : ℕ) : Subgroup (BinaryPower n ≃ₗ[ZMod 2] BinaryPower n) :=
  finitary (binaryPowerBasis n)

/-- The printed membership condition: `g - I` has finite matrix support in the
standard basis of `V^n`. -/
theorem mem_binaryGLfs_iff (n : ℕ) (g : BinaryPower n ≃ₗ[ZMod 2] BinaryPower n) :
    g ∈ binaryGLfs n ↔
      (matrixSupport (binaryPowerBasis n) ((g : BinaryPower n →ₗ[ZMod 2] BinaryPower n) -
        LinearMap.id)).Finite :=
  mem_finitary_iff_finite_matrixSupport _ g

/-- A bijection `Σ (i : Fin n), ℕ ≃ ℕ` for `n ≥ 1`. -/
noncomputable def powerIndexEquiv (n : ℕ) [NeZero n] : (Σ _ : Fin n, ℕ) ≃ ℕ := by
  haveI : Infinite (Σ _ : Fin n, ℕ) :=
    Infinite.of_injective (fun k : ℕ ↦ (⟨0, k⟩ : Σ _ : Fin n, ℕ))
      fun a b h ↦ by simpa using h
  haveI := Denumerable.ofEncodableOfInfinite (Σ _ : Fin n, ℕ)
  exact Denumerable.eqv _

/-- **`GL_fs(V^n) ≅ ⋃_N SL_N(F_2)`** for `n ≥ 1`. -/
noncomputable def binaryGLfsEquivSLUnion (n : ℕ) [NeZero n] : binaryGLfs n ≃* binarySLUnion :=
  (finitaryEquivOfBasis (binaryPowerBasis n) binaryBasis (powerIndexEquiv n)
      (e := (binaryPowerBasis n).equiv binaryBasis (powerIndexEquiv n))
      fun b ↦ Module.Basis.equiv_apply _ _ _ _).trans
    (MulEquiv.subgroupCongr binarySLUnion_eq_finitary.symm)

end FinitaryLinear
end GroupApproximation

#audit_axioms GroupApproximation.FinitaryLinear.conjAut_map_finitary
#audit_axioms GroupApproximation.FinitaryLinear.mem_binaryGLfs_iff
