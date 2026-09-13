import GroupApproximation.KTheory.TensorProduct
import GroupApproximation.KTheory.Functorial

/-!
# Naturality of the external product on `K₀`

Let `μ : A × B → C` and `μ' : A' × B' → C'` be star pairings, and let `f : A → A'`,
`g : B → B'`, `h : C → C'` be coefficient `*`-homomorphisms with
`h (μ a b) = μ' (f a) (g b)`.  Entrywise application then commutes with the Kronecker product
(`kron_map`), so on `K₀`

  `KZero.map h (extProd μ x y) = extProd μ' (KZero.map f x) (KZero.map g y)`
  (`KZero.map_extProd`).

For the minimal tensor product this is the naturality of `K₀(A) × K₀(B) → K₀(A ⊗ B)` in each
variable (Blackadar, *K-Theory for Operator Algebras*, §9.2).  For the unit: when `μ 1 1 = 1`,
the external product of the classes of `1_m` and `1_n` is the class of `1_{mn}`
(`KZero.extProd_mk_one`).
-/

noncomputable section

namespace GroupApproximation
namespace KTheory

section NonUnital

variable {A B C A' B' C' : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B]
  [StarRing B] [NonUnitalSemiring C] [StarRing C] [NonUnitalSemiring A'] [StarRing A']
  [NonUnitalSemiring B'] [StarRing B'] [NonUnitalSemiring C'] [StarRing C']

/-- Entrywise application of compatible `*`-homomorphisms commutes with the Kronecker
product. -/
theorem kron_map (μ : StarPairing A B C) (μ' : StarPairing A' B' C') (f : A →⋆ₙ+* A')
    (g : B →⋆ₙ+* B') (h : C →⋆ₙ+* C') (hμ : ∀ a b, h (μ.toFun a b) = μ'.toFun (f a) (g b))
    {m n : ℕ} (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) B) :
    (kron μ p q).map h = kron μ' (p.map f) (q.map g) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.map_apply, kron_apply, hμ]

/-- Transport of an external product of cycles along compatible `*`-homomorphisms. -/
theorem Cycle.map_extProd (μ : StarPairing A B C) (μ' : StarPairing A' B' C')
    (f : A →⋆ₙ+* A') (g : B →⋆ₙ+* B') (h : C →⋆ₙ+* C')
    (hμ : ∀ a b, h (μ.toFun a b) = μ'.toFun (f a) (g b)) (x : Cycle A) (y : Cycle B) :
    (Cycle.extProd μ x y).map h = Cycle.extProd μ' (x.map f) (y.map g) :=
  Cycle.eq_of_proj_eq (kron_map μ μ' f g h hμ x.proj y.proj)

namespace KZero

private theorem kzero_hom_ext {D : Type*} [NonUnitalSemiring D] [StarRing D] {G : Type*}
    [AddCommGroup G] {φ ψ : KZero D →+ G} (hφψ : ∀ x : Cycle D, φ (mk x) = ψ (mk x)) :
    φ = ψ := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  exact AddMonoidHom.ext fun v => Quotient.inductionOn v fun x => hφψ x

private theorem kzero_map_id_apply {D : Type*} [NonUnitalSemiring D] [StarRing D]
    (b : KZero D) : map (NonUnitalStarRingHom.id D) b = b := by
  have key : map (NonUnitalStarRingHom.id D) = AddMonoidHom.id (KZero D) :=
    kzero_hom_ext fun x => by
      rw [map_mk, AddMonoidHom.id_apply]
      obtain ⟨n, p, hp⟩ := x
      exact congrArg mk (Cycle.eq_of_proj_eq (Matrix.ext fun _ _ => rfl))
  exact DFunLike.congr_fun key b

/-- **Naturality of the external product on `K₀`** for compatible coefficient
`*`-homomorphisms. -/
theorem map_extProd (μ : StarPairing A B C) (μ' : StarPairing A' B' C') (f : A →⋆ₙ+* A')
    (g : B →⋆ₙ+* B') (h : C →⋆ₙ+* C') (hμ : ∀ a b, h (μ.toFun a b) = μ'.toFun (f a) (g b))
    (a : KZero A) (b : KZero B) :
    map h (extProd μ a b) = extProd μ' (map f a) (map g b) := by
  have key : (AddMonoidHom.compHom (map h) :
        (KZero B →+ KZero C) →+ (KZero B →+ KZero C')).comp (extProd μ) =
      (AddMonoidHom.compHom' (map g) :
        (KZero B' →+ KZero C') →+ (KZero B →+ KZero C')).comp ((extProd μ').comp (map f)) :=
    kzero_hom_ext fun x => kzero_hom_ext fun y => by
      show map h (extProd μ (mk x) (mk y)) = extProd μ' (map f (mk x)) (map g (mk y))
      rw [extProd_mk, map_mk, map_mk, map_mk, extProd_mk, Cycle.map_extProd μ μ' f g h hμ]
  exact DFunLike.congr_fun (DFunLike.congr_fun key a) b

/-- Naturality in the left variable only, the right coefficient ring being fixed. -/
theorem map_extProd_left (μ : StarPairing A B C) (ν : StarPairing A' B C') (f : A →⋆ₙ+* A')
    (h : C →⋆ₙ+* C') (hν : ∀ a b, h (μ.toFun a b) = ν.toFun (f a) b)
    (a : KZero A) (b : KZero B) :
    map h (extProd μ a b) = extProd ν (map f a) b := by
  rw [map_extProd μ ν f (NonUnitalStarRingHom.id B) h hν, kzero_map_id_apply]

end KZero

end NonUnital

section Unital

variable {A B C : Type*} [Semiring A] [StarRing A] [Semiring B] [StarRing B] [Semiring C]
  [StarRing C]

/-- The external product of the unit cycles of sizes `m` and `n` is the unit cycle of size
`m * n`, for a unital pairing. -/
theorem Cycle.extProd_one (μ : StarPairing A B C) (hμ : μ.toFun 1 1 = 1) (m n : ℕ) :
    Cycle.extProd μ (⟨m, 1, IsStarProjection.one _⟩ : Cycle A)
        (⟨n, 1, IsStarProjection.one _⟩ : Cycle B) =
      (⟨m * n, 1, IsStarProjection.one _⟩ : Cycle C) :=
  Cycle.eq_of_proj_eq (kron_one_one (m := m) (n := n) μ hμ)

/-- `[1_m] × [1_n] ↦ [1_{mn}]`, for a unital pairing. -/
theorem KZero.extProd_mk_one (μ : StarPairing A B C) (hμ : μ.toFun 1 1 = 1) (m n : ℕ) :
    KZero.extProd μ (KZero.mk (⟨m, 1, IsStarProjection.one _⟩ : Cycle A))
        (KZero.mk (⟨n, 1, IsStarProjection.one _⟩ : Cycle B)) =
      KZero.mk (⟨m * n, 1, IsStarProjection.one _⟩ : Cycle C) := by
  rw [KZero.extProd_mk, Cycle.extProd_one μ hμ]

end Unital

end KTheory
end GroupApproximation
