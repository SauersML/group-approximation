import Mathlib.Algebra.CharP.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity: block-diagonal assembly (lane bh-met-42)

Given finitely many `Q`-equivariant maps `φ_j : W →+ K_j^{d_j}` (with `Q` acting on `K_j^{d_j}`
through matrices `ρ_j`) that jointly detect `0`, and field embeddings `f_j : K_j →+* L` into a
common field `L` of characteristic zero, we obtain one `Q`-equivariant injective map
`W →+ L^d` with `Q` acting through `GL_d(L)`: push everything into `L`, take the product
`V = ∏_j L^{d_j}` with the block-diagonal action, and choose a basis of `V`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- The block-diagonal action of `Q` on `∏_j L^{d_j}`. -/
noncomputable def blockEnd {Q J L : Type} [Monoid Q] [Field L] {d : J → ℕ}
    (ρ : ∀ j, Q →* Matrix.GeneralLinearGroup (Fin (d j)) L) :
    Q →* Module.End L (∀ j, Fin (d j) → L) where
  toFun q := LinearMap.pi fun j =>
    (ρ j q : Matrix (Fin (d j)) (Fin (d j)) L).mulVecLin.comp
      (LinearMap.proj (R := L) (φ := fun j => Fin (d j) → L) j)
  map_one' := LinearMap.ext fun v => funext fun j => by
    show (ρ j 1 : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ v j = v j
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  map_mul' a b := LinearMap.ext fun v => funext fun j => by
    show (ρ j (a * b) : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ v j =
      (ρ j a : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ
        ((ρ j b : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ v j)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.blockEnd

/-- An equivariant injection into a finite-dimensional representation gives a matrix
representation, by choosing a basis. -/
theorem exists_matrix_of_end {Q W V L : Type} [Group Q] [AddCommGroup W] [Field L]
    [AddCommGroup V] [Module L V] [Module.Finite L V] (act : Q → W → W)
    (ρ : Q →* Module.End L V) (ι : W →+ V) (hinj : Function.Injective ι)
    (hequiv : ∀ q w, ι (act q w) = ρ q (ι w)) :
    ∃ (d : ℕ) (ρ' : Q →* Matrix.GeneralLinearGroup (Fin d) L) (ι' : W →+ (Fin d → L)),
      Function.Injective ι' ∧
        ∀ q w, ι' (act q w) = Matrix.mulVec (ρ' q : Matrix (Fin d) (Fin d) L) (ι' w) := by
  let b := Module.finBasis L V
  refine ⟨Module.finrank L V,
    ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ).toHomUnits,
    b.equivFun.toLinearMap.toAddMonoidHom.comp ι, ?_, fun q w => ?_⟩
  · exact b.equivFun.injective.comp hinj
  · change b.equivFun (ι (act q w)) = LinearMap.toMatrix b b (ρ q) *ᵥ b.equivFun (ι w)
    rw [hequiv]
    simp only [Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (ρ q) (ι w)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_matrix_of_end

/-- Finitely many equivariant pieces over one field `L` that jointly detect `0` combine into
one equivariant injection with a matrix representation. -/
theorem exists_linearization_of_pieces {Q W J L : Type} [Group Q] [AddCommGroup W] [Fintype J]
    [Field L] (act : Q → W → W) (d : J → ℕ)
    (ρ : ∀ j, Q →* Matrix.GeneralLinearGroup (Fin (d j)) L) (φ : ∀ j, W →+ (Fin (d j) → L))
    (hdet : ∀ w, (∀ j, φ j w = 0) → w = 0)
    (hequiv : ∀ j q w,
      φ j (act q w) = Matrix.mulVec (ρ j q : Matrix (Fin (d j)) (Fin (d j)) L) (φ j w)) :
    ∃ (d' : ℕ) (ρ' : Q →* Matrix.GeneralLinearGroup (Fin d') L) (ι : W →+ (Fin d' → L)),
      Function.Injective ι ∧
        ∀ q w, ι (act q w) = Matrix.mulVec (ρ' q : Matrix (Fin d') (Fin d') L) (ι w) := by
  let ι : W →+ (∀ j, Fin (d j) → L) :=
    AddMonoidHom.mk' (fun w j => φ j w) fun a b => funext fun j => map_add (φ j) a b
  refine exists_matrix_of_end act (blockEnd ρ) ι ?_ fun q w => funext fun j => hequiv j q w
  exact (injective_iff_map_eq_zero ι).mpr fun w hw => hdet w fun j => congrFun hw j

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_linearization_of_pieces

/-- The same, with the pieces over different fields `K j` embedded into `L`. -/
theorem exists_linearization_of_field_pieces {Q W J L : Type} [Group Q] [AddCommGroup W]
    [Fintype J] [Field L] (act : Q → W → W) (K : J → Type) [∀ j, Field (K j)]
    (f : ∀ j, K j →+* L) (d : J → ℕ)
    (ρ : ∀ j, Q →* Matrix.GeneralLinearGroup (Fin (d j)) (K j))
    (φ : ∀ j, W →+ (Fin (d j) → K j)) (hdet : ∀ w, (∀ j, φ j w = 0) → w = 0)
    (hequiv : ∀ j q w,
      φ j (act q w) = Matrix.mulVec (ρ j q : Matrix (Fin (d j)) (Fin (d j)) (K j)) (φ j w)) :
    ∃ (d' : ℕ) (ρ' : Q →* Matrix.GeneralLinearGroup (Fin d') L) (ι : W →+ (Fin d' → L)),
      Function.Injective ι ∧
        ∀ q w, ι (act q w) = Matrix.mulVec (ρ' q : Matrix (Fin d') (Fin d') L) (ι w) := by
  refine exists_linearization_of_pieces act d
    (fun j => (Matrix.GeneralLinearGroup.map (f j)).comp (ρ j))
    (fun j => AddMonoidHom.mk' (fun w k => f j (φ j w k)) fun a b => funext fun k => by
      show f j (φ j (a + b) k) = f j (φ j a k) + f j (φ j b k)
      rw [map_add, Pi.add_apply, map_add])
    (fun w hw => hdet w fun j => funext fun k => ?_) (fun j q w => funext fun k => ?_)
  · have hk : f j (φ j w k) = f j 0 := by
      rw [map_zero]
      exact congrFun (hw j) k
    exact (f j).injective hk
  · show f j (φ j (act q w) k) =
      ((ρ j q : Matrix (Fin (d j)) (Fin (d j)) (K j)).map (f j) *ᵥ (f j ∘ φ j w)) k
    rw [hequiv, RingHom.map_mulVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_linearization_of_field_pieces

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
