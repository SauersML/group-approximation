import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary

/-!
# Absorbing extensions with vanishing class split up to unitary equivalence

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`.

This file covers the extension theory used in the last step of Schafhauser's proof of the
Tikuisis–White–Winter theorem (C. Schafhauser, *A new proof of the Tikuisis–White–Winter
theorem*, J. reine angew. Math. 759 (2020), §5). It follows the absorption framework of
G. A. Elliott and D. Kucerovsky, *An abstract Voiculescu–Brown–Douglas–Fillmore absorption
theorem*, Pacific J. Math. 198 (2001).

An extension of `S` is given in its Busby form: a unital `⋆`-homomorphism `θ : S →⋆ₐ[R] Q`
into a quotient `π : E →⋆ₐ[R] Q` of a unital ambient algebra `E`. We never need `π` to be
surjective. Everything here is pure unital `⋆`-ring algebra, so it applies both to the
corona `M(J ⊗ 𝒦)/(J ⊗ 𝒦)` and to the matrix corona.

* `IsUnitarilyEquivalentBusby`: `θ' = Ad u ∘ θ` for a unitary `u ∈ Q`.
  `IsStronglyUnitarilyEquivalentBusby` requires `u = π v` with `v` unitary in `E`.
* `BusbyCuntzPair`: a pair of isometries `s₁, s₂` with `s₁ s₁* + s₂ s₂* = 1`.
  `BusbyCuntzPair.sumBusby`: the direct sum `θ ⊕ θ' = s₁ θ(·) s₁* + s₂ θ'(·) s₂*`.
  The sum does not depend on the pair up to unitary equivalence
  (`isUnitarilyEquivalentBusby_sumBusby_pair`), is commutative (`..._sumBusby_comm`) and respects
  unitary equivalence (`..._sumBusby_congr`). A sum of trivial extensions is trivial
  (`isTrivialBusby_sumBusby`).
* `IsAbsorbingBusby`, `IsStablyTrivialBusby`, and the main result
  `exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby`: an absorbing extension that is
  stably trivial (in particular one with zero class under the "absorbing modulo split" picture of
  `KK¹`) is unitarily equivalent to a trivial one (Elliott–Kucerovsky 2001; Schafhauser 2020,
  §5). `isTrivialBusby_of_isStronglyAbsorbingBusby_of_isStablyTrivialBusby` is the strong form.
* `busby_trace_conj_eq`, `trace_lift_eq_of_isAbsorbingBusby_of_isStablyTrivialBusby`: tracial
  functionals do not see the unitary conjugation, so the lift has the same traces as `θ`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

section Conjugation

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- Conjugating a unital `⋆`-homomorphism by a unitary, `Ad u ∘ θ`. -/
def busbyConj (u : Q) (hu : u ∈ unitary Q) (θ : S →⋆ₐ[R] Q) : S →⋆ₐ[R] Q where
  toFun s := u * θ s * star u
  map_one' := by
    show u * θ 1 * star u = 1
    rw [map_one θ, mul_one, Unitary.mul_star_self_of_mem hu]
  map_mul' x y := by
    show u * θ (x * y) * star u = u * θ x * star u * (u * θ y * star u)
    rw [map_mul θ x y]
    simp only [mul_assoc]
    rw [← mul_assoc (star u) u, Unitary.star_mul_self_of_mem hu, one_mul]
  map_zero' := by
    show u * θ 0 * star u = 0
    rw [map_zero θ, mul_zero, zero_mul]
  map_add' x y := by
    show u * θ (x + y) * star u = u * θ x * star u + u * θ y * star u
    rw [map_add θ x y, mul_add, add_mul]
  commutes' r := by
    show u * θ (algebraMap R S r) * star u = algebraMap R Q r
    rw [AlgHomClass.commutes θ r, ← Algebra.commutes r u, mul_assoc,
      Unitary.mul_star_self_of_mem hu, mul_one]
  map_star' x := by
    show u * θ (star x) * star u = star (u * θ x * star u)
    rw [map_star θ x, star_mul, star_mul, star_star, mul_assoc]

theorem busbyConj_apply (u : Q) (hu : u ∈ unitary Q) (θ : S →⋆ₐ[R] Q) (s : S) :
    busbyConj u hu θ s = u * θ s * star u := rfl

/-- `u* (u x u*) u = x` for a unitary `u`. -/
theorem busby_star_conj_conj {u : Q} (hu : u ∈ unitary Q) (x : Q) :
    star u * (u * x * star u) * u = x := by
  simp only [mul_assoc]
  rw [Unitary.star_mul_self_of_mem hu, mul_one, ← mul_assoc, Unitary.star_mul_self_of_mem hu,
    one_mul]

/-- Conjugating a conjugate by a product: `w (a x a*) w* = (w a) x (w a)*`. -/
theorem busby_conj_mul (w a x : Q) : w * (a * x * star a) * star w = w * a * x * star (w * a) := by
  rw [star_mul]
  simp only [mul_assoc]

/-- Tracial functionals are invariant under unitary conjugation. This is the reason the lift
obtained from absorption has the same traces as the extension (Schafhauser 2020, §5). -/
theorem busby_trace_conj_eq {M : Type*} {τ : Q → M} (hτ : ∀ x y : Q, τ (x * y) = τ (y * x))
    {u : Q} (hu : u ∈ unitary Q) (x : Q) : τ (u * x * star u) = τ x := by
  rw [hτ (u * x) (star u), ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]

/-- Two extensions (Busby maps) are unitarily equivalent if one is `Ad u` of the other for a
unitary `u` of the quotient (Elliott–Kucerovsky 2001, §1). -/
abbrev IsUnitarilyEquivalentBusby (θ θ' : S →⋆ₐ[R] Q) : Prop :=
  ∃ u ∈ unitary Q, ∀ s, θ' s = u * θ s * star u

theorem IsUnitarilyEquivalentBusby.refl (θ : S →⋆ₐ[R] Q) : IsUnitarilyEquivalentBusby θ θ :=
  ⟨1, one_mem _, fun s => by rw [one_mul, star_one, mul_one]⟩

theorem IsUnitarilyEquivalentBusby.symm {θ θ' : S →⋆ₐ[R] Q}
    (h : IsUnitarilyEquivalentBusby θ θ') : IsUnitarilyEquivalentBusby θ' θ := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨star u, Unitary.star_mem hu, fun s => ?_⟩
  rw [h s, star_star]
  exact (busby_star_conj_conj hu (θ s)).symm

theorem IsUnitarilyEquivalentBusby.trans {θ θ' θ'' : S →⋆ₐ[R] Q}
    (h₁ : IsUnitarilyEquivalentBusby θ θ') (h₂ : IsUnitarilyEquivalentBusby θ' θ'') :
    IsUnitarilyEquivalentBusby θ θ'' := by
  obtain ⟨u, hu, h₁⟩ := h₁
  obtain ⟨v, hv, h₂⟩ := h₂
  refine ⟨v * u, mul_mem hv hu, fun s => ?_⟩
  rw [h₂ s, h₁ s, star_mul]
  simp only [mul_assoc]

theorem isUnitarilyEquivalentBusby_busbyConj (u : Q) (hu : u ∈ unitary Q) (θ : S →⋆ₐ[R] Q) :
    IsUnitarilyEquivalentBusby θ (busbyConj u hu θ) :=
  ⟨u, hu, fun _ => rfl⟩

/-- Unitary equivalence preserves every tracial functional of the Busby map. -/
theorem IsUnitarilyEquivalentBusby.trace_eq {M : Type*} {τ : Q → M}
    (hτ : ∀ x y : Q, τ (x * y) = τ (y * x)) {θ θ' : S →⋆ₐ[R] Q}
    (h : IsUnitarilyEquivalentBusby θ θ') (s : S) : τ (θ' s) = τ (θ s) := by
  obtain ⟨u, hu, h⟩ := h
  rw [h s, busby_trace_conj_eq hτ hu]

end Conjugation

section Ambient

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- Strong unitary equivalence: the implementing unitary lifts to a unitary of the ambient
algebra `E` (Elliott–Kucerovsky 2001, §1). -/
abbrev IsStronglyUnitarilyEquivalentBusby (π : E →⋆ₐ[R] Q) (θ θ' : S →⋆ₐ[R] Q) : Prop :=
  ∃ v ∈ unitary E, ∀ s, θ' s = π v * θ s * star (π v)

theorem IsStronglyUnitarilyEquivalentBusby.refl (π : E →⋆ₐ[R] Q) (θ : S →⋆ₐ[R] Q) :
    IsStronglyUnitarilyEquivalentBusby π θ θ :=
  ⟨1, one_mem _, fun s => by rw [map_one π, one_mul, star_one, mul_one]⟩

theorem IsStronglyUnitarilyEquivalentBusby.symm {π : E →⋆ₐ[R] Q} {θ θ' : S →⋆ₐ[R] Q}
    (h : IsStronglyUnitarilyEquivalentBusby π θ θ') : IsStronglyUnitarilyEquivalentBusby π θ' θ := by
  obtain ⟨v, hv, h⟩ := h
  refine ⟨star v, Unitary.star_mem hv, fun s => ?_⟩
  rw [map_star π v, star_star, h s]
  exact (busby_star_conj_conj (Unitary.map_mem π hv) (θ s)).symm

theorem IsStronglyUnitarilyEquivalentBusby.trans {π : E →⋆ₐ[R] Q} {θ θ' θ'' : S →⋆ₐ[R] Q}
    (h₁ : IsStronglyUnitarilyEquivalentBusby π θ θ')
    (h₂ : IsStronglyUnitarilyEquivalentBusby π θ' θ'') :
    IsStronglyUnitarilyEquivalentBusby π θ θ'' := by
  obtain ⟨u, hu, h₁⟩ := h₁
  obtain ⟨v, hv, h₂⟩ := h₂
  refine ⟨v * u, mul_mem hv hu, fun s => ?_⟩
  rw [h₂ s, h₁ s, map_mul π v u, star_mul]
  simp only [mul_assoc]

theorem IsStronglyUnitarilyEquivalentBusby.isUnitarilyEquivalentBusby {π : E →⋆ₐ[R] Q}
    {θ θ' : S →⋆ₐ[R] Q} (h : IsStronglyUnitarilyEquivalentBusby π θ θ') :
    IsUnitarilyEquivalentBusby θ θ' := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨π v, Unitary.map_mem π hv, h⟩

/-- An extension is trivial (split) if its Busby map lifts to a unital `⋆`-homomorphism into the
ambient algebra. -/
abbrev IsTrivialBusby (π : E →⋆ₐ[R] Q) (θ : S →⋆ₐ[R] Q) : Prop :=
  ∃ ψ : S →⋆ₐ[R] E, ∀ s, π (ψ s) = θ s

/-- Triviality passes along strong unitary equivalence: conjugate the lift. -/
theorem IsTrivialBusby.of_isStronglyUnitarilyEquivalentBusby {π : E →⋆ₐ[R] Q}
    {θ θ' : S →⋆ₐ[R] Q} (ht : IsTrivialBusby π θ) (h : IsStronglyUnitarilyEquivalentBusby π θ θ') :
    IsTrivialBusby π θ' := by
  obtain ⟨ψ, hψ⟩ := ht
  obtain ⟨v, hv, h⟩ := h
  refine ⟨busbyConj v hv ψ, fun s => ?_⟩
  rw [busbyConj_apply, map_mul π (v * ψ s) (star v), map_mul π v (ψ s), map_star π v, hψ s, h s]

end Ambient

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

section Absorption

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- `θ` absorbs the trivial extensions whose lifts lie in `𝒯`: `θ ⊕ π ∘ σ ≃ θ` for every `σ ∈ 𝒯`
(Elliott–Kucerovsky 2001, Definition 2; Schafhauser 2020, §5). Typical classes `𝒯`: all unital
`⋆`-homomorphisms, or those that are weakly nuclear. -/
abbrev IsAbsorbingBusby (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair Q) (𝒯 : Set (S →⋆ₐ[R] E))
    (θ : S →⋆ₐ[R] Q) : Prop :=
  ∀ σ ∈ 𝒯, IsUnitarilyEquivalentBusby (P.sumBusby θ (π.comp σ)) θ

/-- Strong absorption: the implementing unitaries lift to `E`. -/
abbrev IsStronglyAbsorbingBusby (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair Q) (𝒯 : Set (S →⋆ₐ[R] E))
    (θ : S →⋆ₐ[R] Q) : Prop :=
  ∀ σ ∈ 𝒯, IsStronglyUnitarilyEquivalentBusby π (P.sumBusby θ (π.comp σ)) θ

/-- `θ` is stably trivial if adding some trivial extension from `𝒯` makes it trivial. This is how
a vanishing class in `Ext(S, J) = KK¹(S, J)` enters: `[θ] = 0` means `θ ⊕ τ` is split for a
trivial `τ` (Schafhauser 2020, §5; Blackadar, *K-theory*, §15.6). -/
abbrev IsStablyTrivialBusby (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair Q) (𝒯 : Set (S →⋆ₐ[R] E))
    (θ : S →⋆ₐ[R] Q) : Prop :=
  ∃ σ ∈ 𝒯, IsTrivialBusby π (P.sumBusby θ (π.comp σ))

theorem IsStronglyAbsorbingBusby.isAbsorbingBusby {π : E →⋆ₐ[R] Q} {P : BusbyCuntzPair Q}
    {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q} (h : IsStronglyAbsorbingBusby π P 𝒯 θ) :
    IsAbsorbingBusby π P 𝒯 θ :=
  fun σ hσ => (h σ hσ).isUnitarilyEquivalentBusby

/-- **Absorbing plus stably trivial implies trivial up to unitary equivalence**
(Elliott–Kucerovsky 2001; Schafhauser 2020, §5). If `θ` absorbs `𝒯` and `θ ⊕ π ∘ σ` is split for
some `σ ∈ 𝒯`, then `Ad u ∘ θ = π ∘ ψ` for a unital `⋆`-homomorphism `ψ` and a unitary `u`. -/
theorem exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby {π : E →⋆ₐ[R] Q}
    {P : BusbyCuntzPair Q} {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (habs : IsAbsorbingBusby π P 𝒯 θ) (hst : IsStablyTrivialBusby π P 𝒯 θ) :
    ∃ ψ : S →⋆ₐ[R] E, ∃ u ∈ unitary Q, ∀ s, π (ψ s) = u * θ s * star u := by
  obtain ⟨σ, hσ, ψ, hψ⟩ := hst
  obtain ⟨u, hu, h⟩ := (habs σ hσ).symm
  exact ⟨ψ, u, hu, fun s => (hψ s).trans (h s)⟩

/-- Strong form: if the absorption is implemented by unitaries of `E`, then `θ` is trivial. -/
theorem isTrivialBusby_of_isStronglyAbsorbingBusby_of_isStablyTrivialBusby {π : E →⋆ₐ[R] Q}
    {P : BusbyCuntzPair Q} {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (habs : IsStronglyAbsorbingBusby π P 𝒯 θ) (hst : IsStablyTrivialBusby π P 𝒯 θ) :
    IsTrivialBusby π θ := by
  obtain ⟨σ, hσ, ht⟩ := hst
  exact ht.of_isStronglyUnitarilyEquivalentBusby (habs σ hσ)

/-- **Traces are preserved** by the lift from absorption: for every tracial functional `τ` on the
quotient, `τ ∘ π ∘ ψ = τ ∘ θ` (Schafhauser 2020, §5). -/
theorem trace_lift_eq_of_isAbsorbingBusby_of_isStablyTrivialBusby {π : E →⋆ₐ[R] Q}
    {P : BusbyCuntzPair Q} {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (habs : IsAbsorbingBusby π P 𝒯 θ) (hst : IsStablyTrivialBusby π P 𝒯 θ) {M : Type*}
    {τ : Q → M} (hτ : ∀ x y : Q, τ (x * y) = τ (y * x)) :
    ∃ ψ : S →⋆ₐ[R] E, ∃ u ∈ unitary Q, (∀ s, π (ψ s) = u * θ s * star u) ∧
      ∀ s, τ (π (ψ s)) = τ (θ s) := by
  obtain ⟨ψ, u, hu, h⟩ := exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby habs hst
  exact ⟨ψ, u, hu, h, fun s => by rw [h s, busby_trace_conj_eq hτ hu]⟩

end Absorption

end GroupApproximation.Full.TWWSchafhauser
