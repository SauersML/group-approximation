import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitSum

/-!
# Absorbing extensions with vanishing class split up to unitary equivalence

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`.

This is the extension-theoretic last step of Schafhauser's proof of the Tikuisis–White–Winter
theorem (C. Schafhauser, *A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math.
759 (2020), §5), in the absorption framework of G. A. Elliott and D. Kucerovsky, *An abstract
Voiculescu–Brown–Douglas–Fillmore absorption theorem*, Pacific J. Math. 198 (2001).

* `IsAbsorbingBusby`, `IsStronglyAbsorbingBusby`, `IsStablyTrivialBusby`.
* `exists_lift_conj_of_isAbsorbingBusby_of_isStablyTrivialBusby`: an absorbing extension that is
  stably trivial (in particular one with zero class in `Ext(S, J)`) is unitarily equivalent to a
  trivial one: `Ad u ∘ θ = π ∘ ψ`.
* `isTrivialBusby_of_isStronglyAbsorbingBusby_of_isStablyTrivialBusby`: the strong form.
* `trace_lift_eq_of_isAbsorbingBusby_of_isStablyTrivialBusby`: traces are preserved,
  `τ ∘ π ∘ ψ = τ ∘ θ` for every tracial `τ`.

Unitary equivalence lives in `ObstructionSplitEquiv`, direct sums in `ObstructionSplitSum`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

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
