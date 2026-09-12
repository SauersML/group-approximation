import GroupApproximation.KTheory.Basic

/-!
# Functoriality of `K₀` in the coefficient ring

Every operation the consuming lanes want on `K⁰` of a space -- pullback along a
map of base spaces, restriction to a subspace, evaluation at a point, inclusion
of a corner -- is, on the coefficient side, a non-unital `*`-homomorphism
`C(Y, ℂ) →⋆ₙ+* C(X, ℂ)`.  So functoriality is proved once, for coefficient
`*`-homomorphisms, and every geometric operation is an instance of it.  In
particular `K⁰` is contravariant in the space because `X ↦ C(X, ℂ)` is.

The proof is the same three lines three times: the three elementary moves of
`Cycle.Step` are each preserved by entrywise application of a
`*`-homomorphism, because

* `mvn` -- the implementer transports, `Matrix.map_mul` and `star_map`;
* `reindex` -- `Matrix.submatrix_map` is definitional;
* `pad` -- `blockSum_map`, together with `f 0 = 0`.

Nothing here needs `f` to be unital, injective, or continuous.
-/

namespace GroupApproximation
namespace KTheory

open Matrix

variable {A B : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]

/-! ## Entrywise application of a coefficient `*`-homomorphism -/

/-- Entrywise application of a `*`-homomorphism commutes with the adjoint. -/
theorem star_map (f : A →⋆ₙ+* B) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) :
    star (M.map f) = (star M).map f :=
  (Matrix.conjTranspose_map (f := (f : A → B)) fun x => map_star f x).symm

/-- Entrywise application of a `*`-homomorphism commutes with the block sum. -/
theorem blockSum_map (f : A →⋆ₙ+* B) {m n : ℕ} (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) :
    (blockSum p q).map f = blockSum (p.map f) (q.map f) := by
  simp only [blockSum, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero f)]

/-- Entrywise application of a `*`-homomorphism carries projections to
projections. -/
theorem isStarProjection_map (f : A →⋆ₙ+* B) {n : ℕ} {p : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) : IsStarProjection (p.map f) := by
  refine ⟨?_, ?_⟩
  · show p.map f * p.map f = p.map f
    rw [← Matrix.map_mul, hp.isIdempotentElem.eq]
  · show star (p.map f) = p.map f
    rw [star_map, hp.isSelfAdjoint.star_eq]

/-- Murray--von Neumann equivalence survives entrywise application of a
`*`-homomorphism: the implementer transports. -/
theorem murrayVonNeumannEquiv_map (f : A →⋆ₙ+* B) {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨v.map f, ?_, ?_⟩
  · rw [star_map, ← Matrix.map_mul, hv₁]
  · rw [star_map, ← Matrix.map_mul, hv₂]

namespace Cycle

/-- A cycle transported along a coefficient `*`-homomorphism. -/
def map (f : A →⋆ₙ+* B) (x : Cycle A) : Cycle B :=
  ⟨x.size, x.proj.map f, isStarProjection_map f x.isProj⟩

@[simp] theorem map_size (f : A →⋆ₙ+* B) (x : Cycle A) : (x.map f).size = x.size := rfl

@[simp] theorem map_proj (f : A →⋆ₙ+* B) (x : Cycle A) : (x.map f).proj = x.proj.map f := rfl

theorem map_add (f : A →⋆ₙ+* B) (x y : Cycle A) : (x + y).map f = x.map f + y.map f :=
  eq_of_proj_eq (blockSum_map f x.proj y.proj)

theorem map_zero (f : A →⋆ₙ+* B) : (0 : Cycle A).map f = 0 :=
  eq_of_proj_eq (Matrix.map_zero _ (_root_.map_zero f))

/-- Each of the three elementary moves survives transport. -/
theorem Step.map (f : A →⋆ₙ+* B) {x y : Cycle A} (h : Step x y) :
    Rel (x.map f) (y.map f) := by
  cases h with
  | @mvn n p q hp hq hpq =>
      exact rel_of_step (Step.mvn (murrayVonNeumannEquiv_map f hpq))
  | @reindex n m p hp e =>
      exact rel_reindex_eq (isStarProjection_map f hp)
        (isStarProjection_map f (isStarProjection_submatrix e hp)) e
        (Matrix.submatrix_map _ _ _ _)
  | @pad n p hp a =>
      refine rel_trans (rel_of_step (Step.pad (p := p.map f)
        (hp := isStarProjection_map f hp) a)) ?_
      refine rel_reindex_eq _ _ (Equiv.refl (Fin (n + a))) ?_
      simp [blockSum_map, Matrix.map_zero _ (_root_.map_zero f)]

theorem rel_map (f : A →⋆ₙ+* B) {x y : Cycle A} (h : Rel x y) : Rel (x.map f) (y.map f) := by
  induction h with
  | rel _ _ hxy => exact hxy.map f
  | refl _ => exact rel_refl _
  | symm _ _ _ ih => exact rel_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact rel_trans ih₁ ih₂

end Cycle

namespace VMonoid

/-- The additive map induced on stable isomorphism classes. -/
def map (f : A →⋆ₙ+* B) : VMonoid A →+ VMonoid B where
  toFun := Quotient.map (Cycle.map f) fun _ _ h => Cycle.rel_map f h
  map_zero' := congrArg mk (Cycle.map_zero f)
  map_add' a b := Quotient.inductionOn₂ a b fun x y => congrArg mk (Cycle.map_add f x y)

@[simp] theorem map_mk (f : A →⋆ₙ+* B) (x : Cycle A) : map f (mk x) = mk (x.map f) := rfl

end VMonoid

namespace KZero

/-- **`K₀` is a functor of the coefficient ring.**  Composed with
`X ↦ C(X, ℂ)` this is the contravariant functoriality of `K⁰` in the space. -/
noncomputable def map (f : A →⋆ₙ+* B) : KZero A →+ KZero B :=
  Algebra.GrothendieckAddGroup.lift
    ((Algebra.GrothendieckAddGroup.of).comp (VMonoid.map f))

@[simp] theorem map_mk (f : A →⋆ₙ+* B) (x : Cycle A) : map f (mk x) = mk (x.map f) :=
  DFunLike.congr_fun
    (Algebra.GrothendieckAddGroup.lift.symm_apply_apply
      ((Algebra.GrothendieckAddGroup.of).comp (VMonoid.map f))) (VMonoid.mk x)

end KZero

end KTheory
end GroupApproximation
