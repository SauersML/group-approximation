import GroupApproximation.Analysis.LIXLimitMatrixTransport
import Mathlib.Data.Matrix.Composition
import GroupApproximation.Meta.AxiomGuard

/-!
# Flattening `M₂(M₂(A))` to `M₄(A)`

`diag (u, 1)` lives in `M₂` over the stage algebra, while the null-homotopy that witnesses it
contracting is built in `M₄` over the base, and the `2 + 2` split of the former does not align
with the `3 + 1` split of the latter.  Comparing them needs the flattening

    M₂(M₂(A)) ≃⋆ₐ[ℂ] M₄(A),

which is what this file supplies, together with the transport of `U₀` membership across it in
both directions.

Mathlib has most of it.  `Matrix.compAlgEquiv` is the same map as an *algebra* equivalence, and
`CStarMatrix.reindexₐ` is already a ⋆-algebra equivalence for a reindexing.  The one thing
missing is that `Mathlib/Data/Matrix/Composition.lean` proves no `map_star` for `Matrix.comp`,
so `compAlgEquiv` cannot be upgraded as it stands.  That gap is `matrixComp_star` below, and it
is definitional: both sides of

    comp (star M) (i, k) (j, l) = star (comp M) (i, k) (j, l)

reduce to `star (M j i l k)`, because `star` on a square matrix is the conjugate transpose by
definition at both levels.  Only function extensionality stands between them, so `ext` followed
by `rfl` is the whole proof.

`U₀` membership then transports by `unitaryHom_mem_unitaryComponentOne`, which applies to any
unital ⋆-homomorphism of C⋆-algebras; an equivalence supplies one in each direction, so both
`flatten_mem_unitaryComponentOne` and its inverse are one line each.
-/

namespace GroupApproximation

namespace LIX

universe u

noncomputable section

/- The nested matrix algebra `M₂(M₂(A))` needs the order on `M₂(A)`, which needs the order on
`A`, and the search for either can pick up a competing instance or run out of budget.  Pinning
the spectral pair at high priority — the same two constants the rest of the lane uses — makes
both resolve directly. -/
attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

variable {A : Type u} [CStarAlgebra A]

example : CStarAlgebra (CStarMat 2 A) := inferInstance
example : CStarAlgebra (CStarMat 4 A) := inferInstance
example : CStarAlgebra (CStarMat 2 (CStarMat 2 A)) := inferInstance

/-! ### The missing `map_star` for `Matrix.comp` -/

/-- `Matrix.comp` intertwines the involutions: flattening a block conjugate transpose gives the
conjugate transpose of the flattening.  Definitional at every entry. -/
theorem matrixComp_star (M : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) :
    Matrix.comp (Fin 2) (Fin 2) (Fin 2) (Fin 2) A (star M)
      = star (Matrix.comp (Fin 2) (Fin 2) (Fin 2) (Fin 2) A M) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- `Matrix.compAlgEquiv` upgraded to a ⋆-algebra equivalence, which is what `Matrix.comp`
deserves and `Mathlib/Data/Matrix/Composition.lean` does not provide. -/
def matrixCompStarAlgEquiv (A : Type u) [CStarAlgebra A] :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A) ≃⋆ₐ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  { (Matrix.compAlgEquiv (Fin 2) (Fin 2) A ℂ).toRingEquiv with
    map_star' := matrixComp_star
    map_smul' := fun _ _ => rfl }

/-- `Fin 2 × Fin 2 ≃ Fin 4`.  `finProdFinEquiv` lands in `Fin (2 * 2)`, which is `Fin 4` by
reduction of the numeral. -/
def finTwoTwo : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-! ### The flattening -/

variable (A) in
/-- **The flattening `M₂(M₂(A)) ≃⋆ₐ[ℂ] M₄(A)`**: compose `Matrix.comp` with the reindexing
`Fin 2 × Fin 2 ≃ Fin 4`. -/
def flattenTwoTwo : CStarMat 2 (CStarMat 2 A) ≃⋆ₐ[ℂ] CStarMat 4 A :=
  (matrixCompStarAlgEquiv A).trans (CStarMatrix.reindexₐ ℂ A finTwoTwo)

variable (A) in
/-- The flattening as a unital ⋆-homomorphism. -/
def flattenHom : CStarMat 2 (CStarMat 2 A) →⋆ₐ[ℂ] CStarMat 4 A :=
  (flattenTwoTwo A).toStarAlgHom

variable (A) in
/-- The inverse of the flattening as a unital ⋆-homomorphism. -/
def unflattenHom : CStarMat 4 A →⋆ₐ[ℂ] CStarMat 2 (CStarMat 2 A) :=
  (flattenTwoTwo A).symm.toStarAlgHom

/-! ### Transport of `U₀` across the flattening -/

/-- A null-homotopic unitary of `M₂(M₂(A))` flattens to a null-homotopic unitary of `M₄(A)`. -/
theorem flatten_mem_unitaryComponentOne {v : unitary (CStarMat 2 (CStarMat 2 A))}
    (hv : v ∈ unitaryComponentOne (CStarMat 2 (CStarMat 2 A))) :
    unitaryHom (flattenHom A) v ∈ unitaryComponentOne (CStarMat 4 A) :=
  unitaryHom_mem_unitaryComponentOne (flattenHom A) hv

/-- A null-homotopic unitary of `M₄(A)` unflattens to a null-homotopic unitary of `M₂(M₂(A))`. -/
theorem unflatten_mem_unitaryComponentOne {v : unitary (CStarMat 4 A)}
    (hv : v ∈ unitaryComponentOne (CStarMat 4 A)) :
    unitaryHom (unflattenHom A) v ∈ unitaryComponentOne (CStarMat 2 (CStarMat 2 A)) :=
  unitaryHom_mem_unitaryComponentOne (unflattenHom A) hv

/-! ### Axiom audit -/

#audit_axioms flattenTwoTwo
#audit_axioms flatten_mem_unitaryComponentOne
#audit_axioms unflatten_mem_unitaryComponentOne

end

end LIX

end GroupApproximation
