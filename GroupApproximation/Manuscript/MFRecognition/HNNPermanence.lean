import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceTraceBridge

/-!
# `thm:hnn-permanence` and `cor:central-hnn`

This module states the two printed results of section `sec:hnn` of
`mf_recognition_complexity.tex` and assembles their printed proofs from the
three steps.

> **Theorem (HNN permanence with a corona conjugator, `thm:hnn-permanence`).**
> In the situation of `eq:hnn`, suppose that `G` admits a tracial MF
> realization `(A, ρ, τ)`, and that for some norm matrix corona `𝒬` there are
> an injective `*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬` with
> `W ιρ(s) W* = ιρ(θ(s))` for `s ∈ S`.  Then `R` admits a tracial MF
> realization.  In particular, `R` is MF.

> **Corollary (central HNN extensions, `cor:central-hnn`).**  If `G` admits a
> tracial MF realization and `S ≤ G` is any subgroup, then
> `⟨G, t | [t, s] = 1 (s ∈ S)⟩` admits a tracial MF realization.

The printed edge datum `θ : S → G` injective is carried by `(T, phi)` with
`T = θ(S)` and `phi : S ≃* T`; `manuscriptHNNPermanence_ofInjectiveHom` is the
same statement written with `θ` itself.  "Admits a tracial MF realization" is
the repository's `IsRegularlyRealized`, and the printed *"In particular, `R` is
MF"* is `IsOperatorMF`.

Every statement below carries the single leading hypothesis
`(hIn : HNNInputs)`, declared in `HNNPermanenceShulman`.  Its first two fields
are the results the manuscript cites — Ueda, Proposition 2.4 and Shulman,
Theorem 16 — and the rest are the printed steps of Step 3 that this
development does not yet close, together with two obligations the manuscript
does not discuss because they are artefacts of the formalization: the
repository's `IsRegularlyRealized` quantifies over realization algebras in
`Type`, while the universal `C*`-HNN algebra of Step 1 necessarily lives one
universe higher; and the corollary's *"`ι` any injective `*`-homomorphism of
`A` into a norm matrix corona"* needs a *unital* such map, while
`HasMFEmbedding` supplies a possibly non-unital one.  Only the conclusions are
the printed ones.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-! ## The assumed inputs

Everything this proof assumes is bundled as `HNNInputs`, declared in
`HNNPermanenceShulman`: the two cited results (Ueda, Proposition 2.4 and
Shulman, Theorem 16) and the printed steps of Step 3 that are still open, each
typed by a named proposition.  Every statement below carries the single leading
hypothesis `(hIn : HNNInputs)`, so the citations and the outstanding
obligations travel with the conclusions; only the conclusions are the printed
ones. -/

/-! ## `thm:hnn-permanence` -/

/-- **`thm:hnn-permanence` (HNN permanence with a corona conjugator).**

Printed: *"In the situation of `eq:hnn`, suppose that `G` admits a tracial MF
realization `(A, ρ, τ)`, and that for some norm matrix corona `𝒬` there are an
injective `*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬` with
`W ιρ(s) W* = ιρ(θ(s))` for `s ∈ S`.  Then `R` admits a tracial MF
realization."*

The proof is the printed three-step proof: Step 1 embeds the universal
`C*`-HNN algebra `U` in the full amalgam `P` (`HNNPermanenceUeda`), Step 2
shows `P`, hence `U`, is MF (`HNNPermanenceShulman`), and Step 3 builds the
tracial MF realization `(A', j, τ')` of `R` inside `U`
(`HNNPermanenceTrace`). -/
theorem manuscriptHNNPermanence (hIn : HNNInputs) {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T phi) := by
  letI : Countable (HNNExtension G S T phi) :=
    hnnExtension_countable hIn G S T phi
  exact hIn.regularRealizationDescent
    (hnnRegularRealization hIn
      ({ realization := realization
         iota := iota
         iota_injective := hiota
         W := W
         conjugates := hW } : CoronaConjugator G S T phi A X))

/-- **`thm:hnn-permanence`, second sentence.**  Printed: *"In particular, `R`
is MF."* -/
theorem manuscriptHNNPermanence_isOperatorMF (hIn : HNNInputs) {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsOperatorMF (HNNExtension G S T phi) := by
  letI : Countable (HNNExtension G S T phi) :=
    hnnExtension_countable hIn G S T phi
  exact isOperatorMF_of_isRegularlyRealized
    (manuscriptHNNPermanence hIn phi realization
      iota hiota W hW)

/-- `thm:hnn-permanence` written with the printed edge homomorphism
`θ : S → G` rather than with Mathlib's edge equivalence: the HNN extension of
`eq:hnn` is `HNNExtension G S θ(S) θ`. -/
theorem manuscriptHNNPermanence_ofInjectiveHom (hIn : HNNInputs) {G : Type} [Group G] [Countable G]
    {S : Subgroup G} (theta : S →* G) (htheta : Function.Injective theta)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho (theta s) : unitary A) : A)) :
    IsRegularlyRealized
      (HNNExtension G S theta.range (MonoidHom.ofInjective htheta)) :=
  manuscriptHNNPermanence hIn
    (MonoidHom.ofInjective htheta) realization iota hiota W hW

/-! ## `cor:central-hnn` -/

/-- **`cor:central-hnn` (central HNN extensions).**

Printed: *"If `G` admits a tracial MF realization and `S ≤ G` is any subgroup,
then `⟨G, t | [t, s] = 1 (s ∈ S)⟩` admits a tracial MF realization."*

Printed proof: *"Apply Theorem `thm:hnn-permanence` with `θ` the inclusion of
`S`, with `ι` any injective `*`-homomorphism of `A` into a norm matrix corona,
and with `W = 1`."*  The presented group is `HNNExtension G S S (id)`, whose
defining relation `t s t⁻¹ = s` is `[t, s] = 1`. -/
theorem manuscriptCentralHNN (hIn : HNNInputs) {G : Type} [Group G] [Countable G]
    (S : Subgroup G) (hG : IsRegularlyRealized G) :
    IsRegularlyRealized (HNNExtension G S S (MulEquiv.refl S)) := by
  obtain ⟨A, instA, ⟨realization⟩⟩ := hG
  letI : CStarAlgebra A := instA
  obtain ⟨X, hX, iota, hiota⟩ :=
    hIn.unitalCoronaEmbedding realization.mf
  letI : ∀ n, Nonempty (X n) := hX
  refine manuscriptHNNPermanence hIn
    (MulEquiv.refl S) realization iota hiota 1 ?_
  intro s
  show (1 : NormMatrixCStarCorona (fun n ↦ X n)) *
        iota ((realization.rho (s : G) : unitary A) : A) *
      star (1 : NormMatrixCStarCorona (fun n ↦ X n)) =
    iota ((realization.rho (s : G) : unitary A) : A)
  rw [one_mul, star_one, mul_one]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
