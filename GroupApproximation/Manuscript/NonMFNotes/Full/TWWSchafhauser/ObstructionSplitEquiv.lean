import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary

/-!
# Unitary equivalence of extensions

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`, first part.

An extension of `S` is given in its Busby form: a unital `⋆`-homomorphism `θ : S →⋆ₐ[R] Q`
into a quotient `π : E →⋆ₐ[R] Q` of a unital ambient algebra `E` (`π` need not be surjective).
Sources: G. A. Elliott and D. Kucerovsky, *An abstract Voiculescu–Brown–Douglas–Fillmore
absorption theorem*, Pacific J. Math. 198 (2001), §1; C. Schafhauser, *A new proof of the
Tikuisis–White–Winter theorem*, J. reine angew. Math. 759 (2020), §5.

* `busbyConj`: `Ad u ∘ θ` for a unitary `u`.
* `IsUnitarilyEquivalentBusby` (unitary in `Q`) and `IsStronglyUnitarilyEquivalentBusby`
  (unitary `π v` with `v ∈ E` unitary): equivalence relations.
* `busby_trace_conj_eq`, `IsUnitarilyEquivalentBusby.trace_eq`: tracial functionals are
  invariant under unitary equivalence.
* `IsTrivialBusby`: the Busby map lifts to a unital `⋆`-homomorphism into `E`. Triviality passes
  along strong unitary equivalence.
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

end GroupApproximation.Full.TWWSchafhauser
