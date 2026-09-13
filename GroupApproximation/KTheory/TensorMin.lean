import GroupApproximation.KTheory.TensorNatural
import GroupApproximation.Analysis.CStarMinTensorInjective

/-!
# The external product into the minimal tensor product

For C*-algebras `A`, `B` the map `(a, b) ↦ a ⊗ b` into the minimal tensor product
`MinTensorProduct A B` is a star pairing (`minPairing`), so `KZero.extProd (minPairing A B)` is
the external product `K₀(A) × K₀(B) → K₀(A ⊗_min B)`, `[p] × [q] ↦ [p ⊗ q]`
(Blackadar, *K-Theory for Operator Algebras*, §9.2; Rørdam–Larsen–Laustsen, Exercise 4.10).
The unit relation `[1_m] × [1_n] = [1_{mn}]` is
`KZero.extProd_mk_one (minPairing A B) (minPairing_one A B)`.

It is natural for the maps of minimal tensor products the repository already has:
* an isometric inclusion `ι : A → C` induces `minTensorInclusion ι : A ⊗_min B → C ⊗_min B`,
  and `K₀(ι ⊗ id) (x × y) = K₀(ι) x × y` (`KZero.map_minTensorInclusion_extProd`);
* a closed two-sided ideal `I ⊆ B` induces `quotientMinTensorMap I : B ⊗_min C → (B/I) ⊗_min C`,
  and `K₀(π ⊗ id) (x × y) = K₀(π) x × y` (`KZero.map_quotientMinTensorMap_extProd`).

`KZero.map` takes coefficient maps `→⋆ₙ+*`; a `⋆`-algebra homomorphism is passed through
`starAlgHomCoeff`.
-/

noncomputable section

universe u v w

namespace GroupApproximation
namespace KTheory

open CStarTensor
open scoped TensorProduct

/-- A `⋆`-algebra homomorphism of C*-algebras, as a coefficient map for `KZero.map`. -/
def starAlgHomCoeff {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y] (φ : X →⋆ₐ[ℂ] Y) :
    X →⋆ₙ+* Y where
  toFun := φ
  map_mul' := map_mul φ
  map_zero' := map_zero φ
  map_add' := map_add φ
  map_star' := map_star φ

@[simp] theorem starAlgHomCoeff_apply {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (φ : X →⋆ₐ[ℂ] Y) (x : X) : starAlgHomCoeff φ x = φ x := rfl

section Pairing

variable (A : Type u) (B : Type v) [CStarAlgebra A] [CStarAlgebra B] [Nontrivial A]
  [Nontrivial B]

/-- The star pairing `(a, b) ↦ a ⊗ b` into the minimal tensor product. -/
def minPairing : StarPairing A B (MinTensorProduct A B) where
  toFun := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => minTensorIn A B (a ⊗ₜ[ℂ] b))
      fun b b' => by
        show minTensorIn A B (a ⊗ₜ[ℂ] (b + b')) =
          minTensorIn A B (a ⊗ₜ[ℂ] b) + minTensorIn A B (a ⊗ₜ[ℂ] b')
        rw [TensorProduct.tmul_add, map_add])
    fun a a' => AddMonoidHom.ext fun b => by
      show minTensorIn A B ((a + a') ⊗ₜ[ℂ] b) =
        minTensorIn A B (a ⊗ₜ[ℂ] b) + minTensorIn A B (a' ⊗ₜ[ℂ] b)
      rw [TensorProduct.add_tmul, map_add]
  map_mul' a a' b b' := by
    show minTensorIn A B ((a * a') ⊗ₜ[ℂ] (b * b')) =
      minTensorIn A B (a ⊗ₜ[ℂ] b) * minTensorIn A B (a' ⊗ₜ[ℂ] b')
    rw [← Algebra.TensorProduct.tmul_mul_tmul]
    exact map_mul (minTensorIn A B) _ _
  map_star' a b := by
    show minTensorIn A B (star a ⊗ₜ[ℂ] star b) = star (minTensorIn A B (a ⊗ₜ[ℂ] b))
    rw [← TensorProduct.star_tmul]
    exact map_star (minTensorIn A B) _

@[simp] theorem minPairing_apply (a : A) (b : B) :
    (minPairing A B).toFun a b = minTensorIn A B (a ⊗ₜ[ℂ] b) := rfl

theorem minPairing_one : (minPairing A B).toFun 1 1 = 1 := by
  show minTensorIn A B ((1 : A) ⊗ₜ[ℂ] (1 : B)) = 1
  rw [← Algebra.TensorProduct.one_def, map_one]

end Pairing

section Inclusion

variable {A : Type u} {C : Type v} {B : Type w} [CStarAlgebra A] [CStarAlgebra C]
  [CStarAlgebra B] [Nontrivial A] [Nontrivial C] [Nontrivial B]

theorem minTensorInclusion_minPairing (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y) (a : A) (b : B) :
    minTensorInclusion (B := B) ι hnorm ((minPairing A B).toFun a b) =
      (minPairing C B).toFun (ι a) b := by
  show minTensorInclusion (B := B) ι hnorm (minTensorIn A B (a ⊗ₜ[ℂ] b)) =
    minTensorIn C B (ι a ⊗ₜ[ℂ] b)
  rw [minTensorInclusion_minTensorIn, tensorStarAlgHomMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

/-- **Naturality of the external product for an isometric inclusion**:
`K₀(ι ⊗ id) (x × y) = K₀(ι) x × y`. -/
theorem KZero.map_minTensorInclusion_extProd (ι : A →⋆ₐ[ℂ] C)
    (hnorm : ∀ y : A ⊗[ℂ] B,
      minTensorNorm (tensorStarAlgHomMap (C := B) ι y) = minTensorNorm y)
    (x : KZero A) (y : KZero B) :
    KZero.map (starAlgHomCoeff (minTensorInclusion (B := B) ι hnorm))
        (KZero.extProd (minPairing A B) x y) =
      KZero.extProd (minPairing C B) (KZero.map (starAlgHomCoeff ι) x) y :=
  KZero.map_extProd_left _ _ _ _ (minTensorInclusion_minPairing ι hnorm) x y

end Inclusion

section Quotient

variable {B : Type u} {C : Type w} [CStarAlgebra B] [CStarAlgebra C] [Nontrivial B]
  [Nontrivial C] (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

theorem quotientMinTensorMap_minPairing (b : B) (c : C) :
    quotientMinTensorMap I ((minPairing B C).toFun b c) =
      (minPairing (B ⧸ I) C).toFun (quotientStarMk I b) c := by
  show quotientMinTensorMap I (minTensorIn B C (b ⊗ₜ[ℂ] c)) =
    minTensorIn (B ⧸ I) C (quotientStarMk I b ⊗ₜ[ℂ] c)
  rw [quotientMinTensorMap_minTensorIn, tensorStarAlgHomMap_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- **Naturality of the external product for a quotient map**:
`K₀(π ⊗ id) (x × y) = K₀(π) x × y`. -/
theorem KZero.map_quotientMinTensorMap_extProd (x : KZero B) (y : KZero C) :
    KZero.map (starAlgHomCoeff (quotientMinTensorMap (C := C) I))
        (KZero.extProd (minPairing B C) x y) =
      KZero.extProd (minPairing (B ⧸ I) C) (KZero.map (starAlgHomCoeff (quotientStarMk I)) x) y :=
  KZero.map_extProd_left _ _ _ _ (quotientMinTensorMap_minPairing I) x y

end Quotient

end KTheory
end GroupApproximation
