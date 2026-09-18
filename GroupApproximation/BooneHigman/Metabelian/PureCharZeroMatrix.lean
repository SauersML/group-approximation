import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import GroupApproximation.BooneHigman.GroupRing.Semidirect
import GroupApproximation.Meta.AxiomGuard

/-!
# Affine groups as matrix groups (lane bh-met-19)

Let `ρ : Q →* GL_n(K)` and let `ι : W →+ Kⁿ` intertwine the `ℤ[Q]`-action on `W` with `ρ`. Then
`(w, q) ↦ [[ρ q, ι w], [0, 1]]` is a homomorphism `Affine ℤ Q W →* GL_{n+1}(K)`. It is injective
when `ρ` and `ι` are.

Endpoints: `kkAffGL`, `kkAffGL_injective`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

section AffMat

variable {Q : Type*} [CommGroup Q] {W : Type*} [AddCommGroup W] [Module (MonoidAlgebra ℤ Q) W]
variable {K : Type*} [Field K] {n : ℕ}
variable (ρ : Q →* Matrix.GeneralLinearGroup (Fin n) K) (ι : W →+ (Fin n → K))

/-- The block matrix `[[ρ q, ι w], [0, 1]]` of an affine element `(w, q)`. -/
def kkAffMat (x : GroupRing.Affine ℤ Q W) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K :=
  Matrix.fromBlocks (ρ x.right : Matrix (Fin n) (Fin n) K)
    (Matrix.of fun i _ => ι (Multiplicative.toAdd x.left) i) 0 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffMat

theorem kkAffMat_mul
    (hι : ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
      Matrix.mulVec (ρ q : Matrix (Fin n) (Fin n) K) (ι w))
    (x y : GroupRing.Affine ℤ Q W) : kkAffMat ρ ι (x * y) = kkAffMat ρ ι x * kkAffMat ρ ι y := by
  simp only [kkAffMat, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, rfl, rfl⟩
  · rw [SemidirectProduct.mul_right, map_mul, Units.val_mul]
  · ext i j
    show ι (Multiplicative.toAdd (x * y).left) i =
      ((ρ x.right : Matrix (Fin n) (Fin n) K) *
        Matrix.of (fun i (_ : Fin 1) => ι (Multiplicative.toAdd y.left) i)) i j +
          ι (Multiplicative.toAdd x.left) i
    rw [GroupRing.toAdd_mul_left, map_add, hι, Pi.add_apply]
    exact add_comm _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffMat_mul

theorem kkAffMat_one : kkAffMat ρ ι 1 = 1 := by
  rw [kkAffMat, ← Matrix.fromBlocks_one]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, rfl, rfl⟩
  · exact congrArg Units.val (map_one ρ)
  · ext i _
    show ι (Multiplicative.toAdd (1 : GroupRing.Affine ℤ Q W).left) i = 0
    exact congrFun (map_zero ι) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffMat_one

/-- `kkAffMat` as a monoid homomorphism into matrices. -/
def kkAffMatHom
    (hι : ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
      Matrix.mulVec (ρ q : Matrix (Fin n) (Fin n) K) (ι w)) :
    GroupRing.Affine ℤ Q W →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K where
  toFun := kkAffMat ρ ι
  map_one' := kkAffMat_one ρ ι
  map_mul' := kkAffMat_mul ρ ι hι

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffMatHom

/-- The affine group `Affine ℤ Q W` acting on `K^{n+1}` by block matrices. -/
def kkAffGL
    (hι : ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
      Matrix.mulVec (ρ q : Matrix (Fin n) (Fin n) K) (ι w)) :
    GroupRing.Affine ℤ Q W →* Matrix.GeneralLinearGroup (Fin (n + 1)) K :=
  (Units.map (Matrix.reindexRingEquiv K
    (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))).toRingHom.toMonoidHom).comp
    (kkAffMatHom ρ ι hι).toHomUnits

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffGL

/-- The block-matrix representation is faithful when `ρ` and `ι` are injective. -/
theorem kkAffGL_injective
    (hι : ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
      Matrix.mulVec (ρ q : Matrix (Fin n) (Fin n) K) (ι w))
    (hρ : Function.Injective ρ) (hι' : Function.Injective ι) :
    Function.Injective (kkAffGL ρ ι hι) := by
  intro x y h
  have h1 : kkAffMat ρ ι x = kkAffMat ρ ι y :=
    (Matrix.reindexRingEquiv K (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))).injective
      (congrArg Units.val h)
  obtain ⟨hA, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h1
  have hl : ι (Multiplicative.toAdd x.left) = ι (Multiplicative.toAdd y.left) :=
    funext fun i => congrFun (congrFun hB i) 0
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective (hι' hl)) (hρ (Units.ext hA))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkAffGL_injective

end AffMat

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
