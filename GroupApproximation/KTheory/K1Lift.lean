import GroupApproximation.KTheory.K1Functorial

/-!
# Lifting `U_0` along surjective ⋆-homomorphisms

A surjective unital ⋆-homomorphism `φ : A → B` of unital C⋆-algebras maps `U_0(A)` onto `U_0(B)`.
Every exponential unitary `exp (i k)`, `k` selfadjoint in `B`, is the image of `exp (i h)` with `h`
the real part of any preimage of `k`, because `φ` commutes with `exp` and with real parts; and
`U_0(B)` consists of finite products of exponential unitaries.  The same holds for the entrywise
maps `M_n(A) → M_n(B)`, which are again surjective unital ⋆-homomorphisms.

* `starAlgHom_map_exp`: `φ (exp x) = exp (φ x)`.
* `exists_expUnitary_lift`, `exists_unitaryComponentOne_lift`: lifting along a surjection.
* `matMapStarAlgHom`, `matMapStarAlgHom_surjective`, `exists_matMapUnitary_lift`.
-/

namespace GroupApproximation

universe u v

noncomputable section

open NormedSpace selfAdjoint

section Lift

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- A ⋆-homomorphism between C⋆-algebras is continuous (it is contractive). -/
theorem continuous_starAlgHom (φ : A →⋆ₐ[ℂ] B) : Continuous φ :=
  AddMonoidHomClass.continuous_of_bound φ 1 fun a => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le φ a

/-- A unital ⋆-homomorphism between C⋆-algebras commutes with the exponential. -/
theorem starAlgHom_map_exp (φ : A →⋆ₐ[ℂ] B) (x : A) : φ (exp x) = exp (φ x) := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  letI : NormedAlgebra ℚ B := .restrictScalars ℚ ℂ B
  exact map_exp φ (continuous_starAlgHom φ) x

/-- The image of an exponential unitary is the exponential unitary of the image. -/
theorem starAlgHom_expUnitary (φ : A →⋆ₐ[ℂ] B) (h : selfAdjoint A) (k : selfAdjoint B)
    (hk : φ (h : A) = (k : B)) : φ (expUnitary h : A) = (expUnitary k : B) := by
  rw [expUnitary_coe, expUnitary_coe, starAlgHom_map_exp, map_smul, hk]

/-- A surjective unital ⋆-homomorphism lifts exponential unitaries to exponential unitaries:
`exp (i k)` is the image of `exp (i h)` for `h` the real part of a preimage of `k`. -/
theorem exists_expUnitary_lift (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Surjective φ)
    (k : selfAdjoint B) : ∃ h : selfAdjoint A, φ (expUnitary h : A) = (expUnitary k : B) := by
  obtain ⟨a, ha⟩ := hφ (k : B)
  refine ⟨realPart a, starAlgHom_expUnitary φ _ k ?_⟩
  rw [map_realPart φ a, ha]
  exact IsSelfAdjoint.coe_realPart (show IsSelfAdjoint (k : B) from k.prop)

/-- **A surjective unital ⋆-homomorphism maps `U_0(A)` onto `U_0(B)`.** -/
theorem exists_unitaryComponentOne_lift (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Surjective φ)
    {u : unitary B} (hu : u ∈ unitaryComponentOne B) :
    ∃ v ∈ unitaryComponentOne A, φ (v : A) = (u : B) := by
  obtain ⟨l, rfl⟩ := mem_unitaryComponentOne_iff_exists_list.mp hu
  clear hu
  induction l with
  | nil =>
    refine ⟨1, (unitaryComponentOne A).one_mem, ?_⟩
    rw [List.map_nil, List.prod_nil]
    exact map_one φ
  | cons k l ih =>
    obtain ⟨v, hv, hvu⟩ := ih
    obtain ⟨h, hh⟩ := exists_expUnitary_lift φ hφ k
    refine ⟨expUnitary h * v,
      (unitaryComponentOne A).mul_mem (expUnitary_mem_unitaryComponentOne h) hv, ?_⟩
    rw [List.map_cons, List.prod_cons]
    show φ ((expUnitary h : A) * (v : A)) = (expUnitary k : B) * ((l.map expUnitary).prod : B)
    rw [map_mul, hh, hvu]

end Lift

section Matrices

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- Entrywise application of `φ` as a unital ⋆-algebra homomorphism `M_n(A) → M_n(B)`. -/
def matMapStarAlgHom (φ : A →⋆ₐ[ℂ] B) (n : ℕ) : CStarMat n A →⋆ₐ[ℂ] CStarMat n B where
  toFun := matMap φ n
  map_one' := (matMapHom φ n).map_one'
  map_mul' := (matMapHom φ n).map_mul'
  map_zero' := by
    ext i j
    exact map_zero φ
  map_add' M N := by
    ext i j
    exact map_add φ (M i j) (N i j)
  commutes' r := by
    ext i j
    show φ ((algebraMap ℂ (CStarMat n A) r) i j) = (algebraMap ℂ (CStarMat n B) r) i j
    rw [CStarMatrix.algebraMap_apply, CStarMatrix.algebraMap_apply]
    split_ifs
    · exact AlgHomClass.commutes φ r
    · exact map_zero φ
  map_star' := (matMapHom φ n).map_star'

theorem matMapStarAlgHom_apply (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (M : CStarMat n A) (i j : Fin n) :
    matMapStarAlgHom φ n M i j = φ (M i j) := rfl

/-- Entrywise application of a surjection is surjective. -/
theorem matMapStarAlgHom_surjective {φ : A →⋆ₐ[ℂ] B} (hφ : Function.Surjective φ) (n : ℕ) :
    Function.Surjective (matMapStarAlgHom φ n) := fun M =>
  ⟨fun i j => Classical.choose (hφ (M i j)),
    CStarMatrix.ext fun i j => Classical.choose_spec (hφ (M i j))⟩

section Order

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- **Entrywise surjections lift `U_0(M_n(B))` to `U_0(M_n(A))`.** -/
theorem exists_matMapUnitary_lift {φ : A →⋆ₐ[ℂ] B} (hφ : Function.Surjective φ) (n : ℕ)
    {u : unitary (CStarMat n B)} (hu : u ∈ unitaryComponentOne (CStarMat n B)) :
    ∃ v ∈ unitaryComponentOne (CStarMat n A), matMapUnitary φ n v = u := by
  obtain ⟨v, hv, hvu⟩ :=
    exists_unitaryComponentOne_lift (matMapStarAlgHom φ n) (matMapStarAlgHom_surjective hφ n) hu
  exact ⟨v, hv, Subtype.ext hvu⟩

end Order

end Matrices

end

end GroupApproximation
