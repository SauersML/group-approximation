import GroupApproximation.Sofic.MarkedCompressionData
import GroupApproximation.Sofic.KazhdanCompressionCore

/-!
# Marked compression from an image inclusion

The operator-norm obstruction never uses a self-map of the Kazhdan group.
It uses only the resulting containment

`t · iota(Γ) · t⁻¹ ⊆ iota(Γ)`.

Recording that weaker datum is essential for finite presentation.  Given a
finitely presented Kazhdan cover `Δ → Γ`, one may choose, for each of the
finitely many generators of `Δ`, an arbitrary lift of its compressed image.
The resulting finite stable-letter relations force the displayed inclusion
even when those chosen lifts do not define an endomorphism of `Δ`.
-/

namespace GroupApproximation

universe u

/-- The exact group-theoretic input used by the analytic marked-compression
argument.  In contrast to `MarkedCompressionData`, no endomorphism of `Γ` is
part of the data: only conjugate-image containment is retained. -/
structure MarkedCompressionInclusionData (Γ : Type) (E : Type u) [Group Γ]
    [Group E] extends KazhdanCompressionCore Γ E where
  /-- The element used to mark two distinct transported lamp sites. -/
  a : Γ
  /-- The marked commutator is an involution. -/
  word_sq : markedCompressionWord t (iota a) c ^ 2 = 1
  /-- The marked commutator is central. -/
  word_central : ∀ g : E, Commute (markedCompressionWord t (iota a) c) g

namespace MarkedCompressionInclusionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- The marked central involution. -/
def word (D : MarkedCompressionInclusionData Γ E) : E :=
  markedCompressionWord D.t (D.iota D.a) D.c

theorem word_pow_two (D : MarkedCompressionInclusionData Γ E) :
    D.word ^ 2 = 1 :=
  D.word_sq

theorem word_commute (D : MarkedCompressionInclusionData Γ E) (g : E) :
    Commute D.word g :=
  D.word_central g

theorem word_inv_eq (D : MarkedCompressionInclusionData Γ E) :
    D.word⁻¹ = D.word := by
  have h := D.word_sq
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_left h

end MarkedCompressionInclusionData

namespace MarkedCompressionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- Every endomorphism-based compression supplies the weaker image-inclusion
data.  This is a lossless conversion for the analytic theorem. -/
def toInclusionData (D : MarkedCompressionData Γ E) :
    MarkedCompressionInclusionData Γ E where
  iota := D.iota
  t := D.t
  c := D.c
  a := D.a
  kazhdan := D.kazhdan
  compresses γ := ⟨D.alpha γ, D.compress γ⟩
  comm_c := D.comm_c
  word_sq := D.word_sq
  word_central := D.word_central

@[simp] theorem toInclusionData_word (D : MarkedCompressionData Γ E) :
    D.toInclusionData.word = D.word :=
  rfl

end MarkedCompressionData

end GroupApproximation
