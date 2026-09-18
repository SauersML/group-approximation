import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitEquiv

/-!
# Direct sums of extensions

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`, second part.

A `BusbyCuntzPair` is a pair of isometries `s₁, s₂` with `s₁ s₁* + s₂ s₂* = 1`. It implements the
direct sum of Busby maps `θ ⊕ θ' = s₁ θ(·) s₁* + s₂ θ'(·) s₂*` (Elliott–Kucerovsky, Pacific J.
Math. 198 (2001), §1; Blackadar, *K-theory for operator algebras*, §15.6; Schafhauser, J. reine
angew. Math. 759 (2020), §5).

* `BusbyCuntzPair.diag`: block-diagonal elements, multiplicative, additive, `⋆`-preserving and
  unital.
* `BusbyCuntzPair.transfer`: the unitary carrying one pair to another.
* `BusbyCuntzPair.sumBusby`: the direct sum. It does not depend on the pair up to unitary
  equivalence (`isUnitarilyEquivalentBusby_sumBusby_pair`), is commutative
  (`isUnitarilyEquivalentBusby_sumBusby_comm`) and respects unitary equivalence
  (`isUnitarilyEquivalentBusby_sumBusby_congr`). A sum of trivial extensions is trivial
  (`isTrivialBusby_sumBusby`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

/-- A pair of isometries with complementary ranges, `s₁* s₁ = s₂* s₂ = 1` and
`s₁ s₁* + s₂ s₂* = 1`. It implements the direct sum of extensions, which is well defined up to
unitary equivalence (Elliott–Kucerovsky 2001, §1; Blackadar, *K-theory*, §15.6). -/
structure BusbyCuntzPair (E : Type*) [Ring E] [StarRing E] where
  /-- The first isometry. -/
  s₁ : E
  /-- The second isometry. -/
  s₂ : E
  star_mul_self₁ : star s₁ * s₁ = 1
  star_mul_self₂ : star s₂ * s₂ = 1
  sum_eq_one : s₁ * star s₁ + s₂ * star s₂ = 1

namespace BusbyCuntzPair

variable {E : Type*} [Ring E] [StarRing E] (P : BusbyCuntzPair E)

theorem star_s₁_mul_s₂ : star P.s₁ * P.s₂ = 0 := by
  have h : star P.s₁ * P.s₂ = star P.s₁ * P.s₂ + star P.s₁ * P.s₂ := by
    calc star P.s₁ * P.s₂ = star P.s₁ * (P.s₁ * star P.s₁ + P.s₂ * star P.s₂) * P.s₂ := by
          rw [P.sum_eq_one, mul_one]
      _ = star P.s₁ * P.s₂ + star P.s₁ * P.s₂ := by
          rw [mul_add, add_mul, ← mul_assoc (star P.s₁) P.s₁ (star P.s₁), P.star_mul_self₁,
            one_mul, mul_assoc (star P.s₁) (P.s₂ * star P.s₂) P.s₂,
            mul_assoc P.s₂ (star P.s₂) P.s₂, P.star_mul_self₂, mul_one]
  exact left_eq_add.mp h

theorem star_s₂_mul_s₁ : star P.s₂ * P.s₁ = 0 := by
  have h := congrArg star P.star_s₁_mul_s₂
  rwa [star_mul, star_star, star_zero] at h

/-- The block-diagonal element `s₁ x s₁* + s₂ y s₂*`. -/
def diag (x y : E) : E := P.s₁ * x * star P.s₁ + P.s₂ * y * star P.s₂

theorem mul₁₁ (x y : E) : P.s₁ * x * star P.s₁ * (P.s₁ * y * star P.s₁) = P.s₁ * (x * y) * star P.s₁ := by
  simp only [mul_assoc]
  rw [← mul_assoc (star P.s₁) P.s₁, P.star_mul_self₁, one_mul]

theorem mul₂₂ (x y : E) : P.s₂ * x * star P.s₂ * (P.s₂ * y * star P.s₂) = P.s₂ * (x * y) * star P.s₂ := by
  simp only [mul_assoc]
  rw [← mul_assoc (star P.s₂) P.s₂, P.star_mul_self₂, one_mul]

theorem mul₁₂ (x y : E) : P.s₁ * x * star P.s₁ * (P.s₂ * y * star P.s₂) = 0 := by
  simp only [mul_assoc]
  rw [← mul_assoc (star P.s₁) P.s₂, P.star_s₁_mul_s₂, zero_mul, mul_zero, mul_zero]

theorem mul₂₁ (x y : E) : P.s₂ * x * star P.s₂ * (P.s₁ * y * star P.s₁) = 0 := by
  simp only [mul_assoc]
  rw [← mul_assoc (star P.s₂) P.s₁, P.star_s₂_mul_s₁, zero_mul, mul_zero, mul_zero]

theorem diag_mul_diag (x y x' y' : E) : P.diag x y * P.diag x' y' = P.diag (x * x') (y * y') := by
  simp only [BusbyCuntzPair.diag]
  rw [add_mul, mul_add, mul_add, P.mul₁₁, P.mul₁₂, P.mul₂₁, P.mul₂₂, add_zero, zero_add]

theorem diag_one : P.diag 1 1 = 1 := by
  simp only [BusbyCuntzPair.diag, mul_one]
  exact P.sum_eq_one

theorem diag_zero : P.diag 0 0 = 0 := by
  simp only [BusbyCuntzPair.diag, mul_zero, zero_mul, add_zero]

theorem diag_add (x y x' y' : E) : P.diag (x + x') (y + y') = P.diag x y + P.diag x' y' := by
  simp only [BusbyCuntzPair.diag, mul_add, add_mul]
  exact add_add_add_comm _ _ _ _

theorem star_diag (x y : E) : star (P.diag x y) = P.diag (star x) (star y) := by
  simp only [BusbyCuntzPair.diag, star_add, star_mul, star_star, mul_assoc]

theorem diag_algebraMap {R : Type*} [CommSemiring R] [Algebra R E] (r : R) :
    P.diag (algebraMap R E r) (algebraMap R E r) = algebraMap R E r := by
  rw [BusbyCuntzPair.diag, ← Algebra.commutes r P.s₁, ← Algebra.commutes r P.s₂,
    mul_assoc (algebraMap R E r) P.s₁ (star P.s₁), mul_assoc (algebraMap R E r) P.s₂ (star P.s₂),
    ← mul_add, P.sum_eq_one, mul_one]

theorem diag_mem_unitary {u v : E} (hu : u ∈ unitary E) (hv : v ∈ unitary E) :
    P.diag u v ∈ unitary E :=
  Unitary.mem_iff.mpr
    ⟨by rw [P.star_diag, P.diag_mul_diag, Unitary.star_mul_self_of_mem hu,
        Unitary.star_mul_self_of_mem hv, P.diag_one],
      by rw [P.star_diag, P.diag_mul_diag, Unitary.mul_star_self_of_mem hu,
        Unitary.mul_star_self_of_mem hv, P.diag_one]⟩

/-- The same pair after swapping the two isometries. -/
def swap : BusbyCuntzPair E where
  s₁ := P.s₂
  s₂ := P.s₁
  star_mul_self₁ := P.star_mul_self₂
  star_mul_self₂ := P.star_mul_self₁
  sum_eq_one := by
    rw [add_comm]
    exact P.sum_eq_one

theorem swap_diag (x y : E) : P.swap.diag x y = P.diag y x := by
  show P.s₂ * x * star P.s₂ + P.s₁ * y * star P.s₁ = P.s₁ * y * star P.s₁ + P.s₂ * x * star P.s₂
  exact add_comm _ _

/-- The unitary `s₁' s₁* + s₂' s₂*` carrying one Cuntz pair to another. -/
def transfer (P P' : BusbyCuntzPair E) : E := P'.s₁ * star P.s₁ + P'.s₂ * star P.s₂

theorem transfer_mul_s₁ (P P' : BusbyCuntzPair E) : transfer P P' * P.s₁ = P'.s₁ := by
  simp only [BusbyCuntzPair.transfer, add_mul, mul_assoc, P.star_mul_self₁, P.star_s₂_mul_s₁,
    mul_one, mul_zero, add_zero]

theorem transfer_mul_s₂ (P P' : BusbyCuntzPair E) : transfer P P' * P.s₂ = P'.s₂ := by
  simp only [BusbyCuntzPair.transfer, add_mul, mul_assoc, P.star_mul_self₂, P.star_s₁_mul_s₂,
    mul_one, mul_zero, zero_add]

theorem star_transfer (P P' : BusbyCuntzPair E) : star (transfer P P') = transfer P' P := by
  simp only [BusbyCuntzPair.transfer, star_add, star_mul, star_star]

theorem transfer_mul_transfer (P P' P'' : BusbyCuntzPair E) :
    transfer P' P'' * transfer P P' = transfer P P'' := by
  show transfer P' P'' * (P'.s₁ * star P.s₁ + P'.s₂ * star P.s₂) =
    P''.s₁ * star P.s₁ + P''.s₂ * star P.s₂
  rw [mul_add, ← mul_assoc (transfer P' P'') P'.s₁, ← mul_assoc (transfer P' P'') P'.s₂,
    transfer_mul_s₁ P' P'', transfer_mul_s₂ P' P'']

theorem transfer_self : transfer P P = 1 := P.sum_eq_one

theorem transfer_mem_unitary (P P' : BusbyCuntzPair E) : transfer P P' ∈ unitary E :=
  Unitary.mem_iff.mpr
    ⟨by rw [star_transfer, transfer_mul_transfer, transfer_self],
      by rw [star_transfer, transfer_mul_transfer, transfer_self]⟩

theorem transfer_conj_diag (P P' : BusbyCuntzPair E) (x y : E) :
    transfer P P' * P.diag x y * star (transfer P P') = P'.diag x y := by
  simp only [BusbyCuntzPair.diag]
  rw [mul_add, add_mul, busby_conj_mul, busby_conj_mul, transfer_mul_s₁, transfer_mul_s₂]

/-- The image of a Cuntz pair under a unital `⋆`-homomorphism. -/
def map {R : Type*} [CommSemiring R] [Algebra R E] {F : Type*} [Ring F] [StarRing F]
    [Algebra R F] (f : E →⋆ₐ[R] F) : BusbyCuntzPair F where
  s₁ := f P.s₁
  s₂ := f P.s₂
  star_mul_self₁ := by rw [← map_star f P.s₁, ← map_mul f (star P.s₁) P.s₁, P.star_mul_self₁, map_one f]
  star_mul_self₂ := by rw [← map_star f P.s₂, ← map_mul f (star P.s₂) P.s₂, P.star_mul_self₂, map_one f]
  sum_eq_one := by
    rw [← map_star f P.s₁, ← map_star f P.s₂, ← map_mul f P.s₁ (star P.s₁),
      ← map_mul f P.s₂ (star P.s₂), ← map_add f (P.s₁ * star P.s₁) (P.s₂ * star P.s₂),
      P.sum_eq_one, map_one f]

theorem map_diag {R : Type*} [CommSemiring R] [Algebra R E] {F : Type*} [Ring F] [StarRing F]
    [Algebra R F] (f : E →⋆ₐ[R] F) (x y : E) : f (P.diag x y) = (P.map f).diag (f x) (f y) := by
  show f (P.s₁ * x * star P.s₁ + P.s₂ * y * star P.s₂) =
    f P.s₁ * f x * star (f P.s₁) + f P.s₂ * f y * star (f P.s₂)
  simp only [map_add, map_mul, map_star]

section Sum

variable {R : Type*} [CommSemiring R] [Algebra R E]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]

/-- The direct sum `θ ⊕ θ'` of two Busby maps, `s ↦ s₁ θ(s) s₁* + s₂ θ'(s) s₂*`
(Elliott–Kucerovsky 2001, §1). -/
def sumBusby (θ θ' : S →⋆ₐ[R] E) : S →⋆ₐ[R] E where
  toFun s := P.diag (θ s) (θ' s)
  map_one' := by
    show P.diag (θ 1) (θ' 1) = 1
    rw [map_one θ, map_one θ', P.diag_one]
  map_mul' x y := by
    show P.diag (θ (x * y)) (θ' (x * y)) = P.diag (θ x) (θ' x) * P.diag (θ y) (θ' y)
    rw [map_mul θ x y, map_mul θ' x y, P.diag_mul_diag]
  map_zero' := by
    show P.diag (θ 0) (θ' 0) = 0
    rw [map_zero θ, map_zero θ', P.diag_zero]
  map_add' x y := by
    show P.diag (θ (x + y)) (θ' (x + y)) = P.diag (θ x) (θ' x) + P.diag (θ y) (θ' y)
    rw [map_add θ x y, map_add θ' x y, P.diag_add]
  commutes' r := by
    show P.diag (θ (algebraMap R S r)) (θ' (algebraMap R S r)) = algebraMap R E r
    rw [AlgHomClass.commutes θ r, AlgHomClass.commutes θ' r, P.diag_algebraMap]
  map_star' x := by
    show P.diag (θ (star x)) (θ' (star x)) = star (P.diag (θ x) (θ' x))
    rw [map_star θ x, map_star θ' x, P.star_diag]

theorem sumBusby_apply (θ θ' : S →⋆ₐ[R] E) (s : S) : P.sumBusby θ θ' s = P.diag (θ s) (θ' s) :=
  rfl

/-- The direct sum respects unitary equivalence in each summand. -/
theorem isUnitarilyEquivalentBusby_sumBusby_congr {θ₁ θ₁' θ₂ θ₂' : S →⋆ₐ[R] E}
    (h₁ : IsUnitarilyEquivalentBusby θ₁ θ₁') (h₂ : IsUnitarilyEquivalentBusby θ₂ θ₂') :
    IsUnitarilyEquivalentBusby (P.sumBusby θ₁ θ₂) (P.sumBusby θ₁' θ₂') := by
  obtain ⟨u, hu, h₁⟩ := h₁
  obtain ⟨v, hv, h₂⟩ := h₂
  refine ⟨P.diag u v, P.diag_mem_unitary hu hv, fun s => ?_⟩
  rw [sumBusby_apply, sumBusby_apply, h₁ s, h₂ s, P.star_diag, P.diag_mul_diag, P.diag_mul_diag]

/-- The direct sum does not depend on the Cuntz pair, up to unitary equivalence. -/
theorem isUnitarilyEquivalentBusby_sumBusby_pair (P' : BusbyCuntzPair E) (θ θ' : S →⋆ₐ[R] E) :
    IsUnitarilyEquivalentBusby (P.sumBusby θ θ') (P'.sumBusby θ θ') :=
  ⟨transfer P P', transfer_mem_unitary P P', fun s => by
    rw [sumBusby_apply, sumBusby_apply, transfer_conj_diag]⟩

/-- The direct sum is commutative up to unitary equivalence. -/
theorem isUnitarilyEquivalentBusby_sumBusby_comm (θ θ' : S →⋆ₐ[R] E) :
    IsUnitarilyEquivalentBusby (P.sumBusby θ θ') (P.sumBusby θ' θ) := by
  obtain ⟨u, hu, h⟩ := P.isUnitarilyEquivalentBusby_sumBusby_pair P.swap θ θ'
  refine ⟨u, hu, fun s => ?_⟩
  rw [← h s, sumBusby_apply, sumBusby_apply, swap_diag]

variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- The direct sum of trivial extensions is trivial: add the lifts with the lifted pair. -/
theorem isTrivialBusby_sumBusby (π : E →⋆ₐ[R] Q) {θ θ' : S →⋆ₐ[R] Q} (ht : IsTrivialBusby π θ)
    (ht' : IsTrivialBusby π θ') : IsTrivialBusby π ((P.map π).sumBusby θ θ') := by
  obtain ⟨ψ, hψ⟩ := ht
  obtain ⟨ψ', hψ'⟩ := ht'
  refine ⟨P.sumBusby ψ ψ', fun s => ?_⟩
  rw [sumBusby_apply, sumBusby_apply, map_diag, hψ s, hψ' s]

end Sum

end BusbyCuntzPair

end GroupApproximation.Full.TWWSchafhauser
