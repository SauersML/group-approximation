import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbSwindle
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Infinite repeats from an amplification

Lane `TWWSch3c2`, work order `WO-TWWSch-3c-2`, second part. Sources: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6; G. G. Kasparov, J. Operator Theory 4
(1980), §7; C. Schafhauser, J. reine angew. Math. 759 (2020), §5. Manuscript label:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (the absorption step).

On a stable multiplier algebra `M = M(J ⊗ 𝒦)`, the infinite repeat `σ∞ = σ ⊕ σ ⊕ ⋯` of a unital
`⋆`-homomorphism `σ : S → M` is `φ ∘ σ` for the amplification `φ(x) = x ⊗ 1`. After identifying
`ℓ²(ℕ) ≅ ℓ²(ℕ) ⊕ ℓ²(ℕ)` with a Cuntz pair `T`, the amplification satisfies
`φ(x) = t₁ φ(x) t₁* + t₂ x t₂*`. This file records that ring-level interface and feeds it into
`ExtensionAbsorbSwindle`:

* `IsBusbyAmplification T φ`: `φ x = T.diag (φ x) x` for every `x`;
* `busby_repeat_of_isBusbyAmplification`: `φ ∘ σ` is an infinite repeat of `σ`;
* `isStronglyAbsorbingBusby_of_amplification` (intertwining form) and
  `isStronglyAbsorbingBusby_of_amplification_compress` (compression form, `d* d = 0 ⇒ d = 0`);
* `cstar_eq_zero_of_star_mul_self_eq_zero` and
  `isStronglyAbsorbingBusby_of_amplification_compress_cstar`: the compression form when the
  corona is a C⋆-ring.

This is how `IsStronglyAbsorbingBusby π' (P.map π') 𝒯 (κ.comp θ)` in the corona square of
`ObstructionSplitCorona` follows, with `π := π'` and `θ := κ.comp θ`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

section Repeat

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]

/-- `φ` is an amplification for the Cuntz pair `T`: `φ(x) = t₁ φ(x) t₁* + t₂ x t₂*`, so that
`φ ≅ φ ⊕ id` (Elliott–Kucerovsky 2001, proof of Thm. 6; Kasparov 1980, §7). -/
abbrev IsBusbyAmplification (T : BusbyCuntzPair E) (φ : E →⋆ₐ[R] E) : Prop :=
  ∀ x, φ x = T.diag (φ x) x

/-- An amplification turns every `⋆`-homomorphism `σ` into an infinite repeat `φ ∘ σ` of `σ`. -/
theorem busby_repeat_of_isBusbyAmplification {T : BusbyCuntzPair E} {φ : E →⋆ₐ[R] E}
    (hφ : IsBusbyAmplification T φ) (σ : S →⋆ₐ[R] E) (s : S) :
    (φ.comp σ) s = T.diag ((φ.comp σ) s) (σ s) :=
  hφ (σ s)

/-- **Absorption from an amplification, intertwining form** (Elliott–Kucerovsky 2001, Thm. 6).
If `θ(s) π(w) = π(w) π(φ(σ(s)))` for an isometry `w` of `E`, for every `σ ∈ 𝒯`, then `θ` is
strongly absorbing. -/
theorem isStronglyAbsorbingBusby_of_amplification (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair E)
    {T : BusbyCuntzPair E} {φ : E →⋆ₐ[R] E} (hφ : IsBusbyAmplification T φ)
    {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (hdom : ∀ σ ∈ 𝒯, ∃ w : E, star w * w = 1 ∧ ∀ s, θ s * π w = π w * π (φ (σ s))) :
    IsStronglyAbsorbingBusby π (P.map π) 𝒯 θ := by
  refine isStronglyAbsorbingBusby_of_dominates π P fun σ hσ => ?_
  obtain ⟨w, hw, hint⟩ := hdom σ hσ
  exact ⟨φ.comp σ, T, busby_repeat_of_isBusbyAmplification hφ σ, w, hw, fun s => hint s⟩

/-- **Absorption from an amplification, compression form.** In a quotient where
`d* d = 0 ⇒ d = 0`, it suffices that `π(w)* θ(s) π(w) = π(φ(σ(s)))` for an isometry `w` of `E`. -/
theorem isStronglyAbsorbingBusby_of_amplification_compress
    (hQ : ∀ d : Q, star d * d = 0 → d = 0) (π : E →⋆ₐ[R] Q) (P : BusbyCuntzPair E)
    {T : BusbyCuntzPair E} {φ : E →⋆ₐ[R] E} (hφ : IsBusbyAmplification T φ)
    {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] Q}
    (hdom : ∀ σ ∈ 𝒯, ∃ w : E, star w * w = 1 ∧ ∀ s, star (π w) * θ s * π w = π (φ (σ s))) :
    IsStronglyAbsorbingBusby π (P.map π) 𝒯 θ := by
  refine isStronglyAbsorbingBusby_of_compress_dominates hQ π P fun σ hσ => ?_
  obtain ⟨w, hw, hcomp⟩ := hdom σ hσ
  exact ⟨φ.comp σ, T, busby_repeat_of_isBusbyAmplification hφ σ, w, hw, fun s => hcomp s⟩

end Repeat

section CStar

/-- In a C⋆-ring, `d* d = 0` forces `d = 0` (the C⋆-identity). -/
theorem cstar_eq_zero_of_star_mul_self_eq_zero {C : Type*} [NonUnitalNormedRing C] [StarRing C]
    [CStarRing C] (d : C) (hd : star d * d = 0) : d = 0 :=
  (CStarRing.star_mul_self_eq_zero_iff d).mp hd

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {C : Type*} [NormedRing C] [StarRing C] [CStarRing C] [Algebra R C]

/-- **Absorption into a C⋆-corona from compression domination of infinite repeats**
(Elliott–Kucerovsky 2001, Thm. 6, algebraic half; Schafhauser 2020, §5). -/
theorem isStronglyAbsorbingBusby_of_amplification_compress_cstar (π : E →⋆ₐ[R] C)
    (P : BusbyCuntzPair E) {T : BusbyCuntzPair E} {φ : E →⋆ₐ[R] E}
    (hφ : IsBusbyAmplification T φ) {𝒯 : Set (S →⋆ₐ[R] E)} {θ : S →⋆ₐ[R] C}
    (hdom : ∀ σ ∈ 𝒯, ∃ w : E, star w * w = 1 ∧ ∀ s, star (π w) * θ s * π w = π (φ (σ s))) :
    IsStronglyAbsorbingBusby π (P.map π) 𝒯 θ := by
  refine isStronglyAbsorbingBusby_of_amplification_compress ?_ π P hφ hdom
  exact fun d hd => cstar_eq_zero_of_star_mul_self_eq_zero d hd

end CStar

end GroupApproximation.Full.TWWSchafhauser
