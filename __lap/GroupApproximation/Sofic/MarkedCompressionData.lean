import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Kazhdan.KazhdanProjection

/-!
# The marked Kazhdan-compression data

This file records the endomorphism-based data used to construct the concrete
marked group.  A `MarkedCompressionData Γ E` records a Kazhdan
group `Γ` mapped into `E`, an element `t` conjugating the image of `Γ` onto
the image of an endomorphism `alpha`, a `Γ`-centralizing element `c`, and a
distinguished `a : Γ`, such that the marked compression word

`w = [t c t⁻¹, (iota a) (t c t⁻¹) (iota a)⁻¹]`

is a central involution of `E`.

Deliberately absent: injectivity of `iota`, properness of `alpha`, and
`a ∉ range alpha`.  Those are only needed to construct groups in which the
marked word is nontrivial.  The analytic theorem is stated against the
strictly weaker `MarkedCompressionInclusionData`, because it consumes only
`t · iota(Γ) · t⁻¹ ⊆ iota(Γ)`.  The conversion is defined in
`MarkedCompressionInclusionData.lean`.
-/

namespace GroupApproximation

universe u

/-- Endomorphism-based construction data for the marked
Kazhdan-compression group `E`. -/
structure MarkedCompressionData (Γ : Type) (E : Type u) [Group Γ]
    [Group E] where
  /-- The comparison homomorphism carrying `Γ` into `E`. -/
  iota : Γ →* E
  /-- The self-compression of `Γ` implemented by `t`. -/
  alpha : Γ →* Γ
  /-- The compressing element. -/
  t : E
  /-- The `Γ`-centralizing element whose `t`-conjugate is marked. -/
  c : E
  /-- The distinguished element of `Γ` separating the two lamp sites. -/
  a : Γ
  /-- Property `(T)` for `Γ`, with representation spaces in `Type 0`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Γ
  /-- `t` conjugates the image of `Γ` onto the image of `alpha`. -/
  compress : ∀ γ : Γ, t * iota γ * t⁻¹ = iota (alpha γ)
  /-- `c` centralizes the image of `Γ`. -/
  comm_c : ∀ γ : Γ, Commute c (iota γ)
  /-- The marked word is an involution. -/
  word_sq : markedCompressionWord t (iota a) c ^ 2 = 1
  /-- The marked word is central. -/
  word_central : ∀ g : E, Commute (markedCompressionWord t (iota a) c) g

namespace MarkedCompressionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]
variable (D : MarkedCompressionData Γ E)

/-- The marked central involution of the data. -/
def word : E := markedCompressionWord D.t (D.iota D.a) D.c

theorem word_pow_two : D.word ^ 2 = 1 := D.word_sq

theorem word_commute (g : E) : Commute D.word g := D.word_central g

theorem word_inv_eq : D.word⁻¹ = D.word := by
  have h := D.word_sq
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_left h

end MarkedCompressionData

end GroupApproximation
