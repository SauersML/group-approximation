import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic

/-!
# Asymptotic lifts whose defects are measured in the reduced product

`ShulmanFill.StarStrongAsymptoticLift` measures its five defects in the norm of
`StarStrong.BoundedStarSequence A`, which is `lp _ ∞` and therefore the supremum
over coordinates.  `Analysis/ShulmanFillNormingPrintedPairCharacter` shows that
this is too strong at finite-dimensional coefficients: a supremum bounds every
fixed coordinate, so `(φ_t ·)ₙ` is an asymptotic homomorphism into `A n` for each
fixed `n`, and when `A n` is finite-dimensional its limit along an ultrafilter is
an honest unital `*`-homomorphism.  At the printed models that yields a character
on `B`, which `B(ℂ²)` has not.

The `*`-strong limit map cannot see finitely many coordinates, so nothing
downstream wants the supremum.  This module records the weaker vocabulary the
repair needs: a defect has to vanish only *in the tail*, uniformly in nothing.

## `TailNull`

`TailNull X` says that for every `ε` there is a stage after which every member
of the family is below `ε` at every large enough coordinate.  Equivalently, the
image of `X t` in the reduced product `∏ₙ A n / ⨁ₙ A n` tends to zero; the
quantifier form is used because the two eventualities are exactly what both the
producers and the consumer of a lift manipulate.

`tailNull_of_tendsto_norm` is the comparison: a defect vanishing in the sup norm
vanishes in the tail.  So `StarStrongAsymptoticLift.toTail` turns every lift in
the old vocabulary into one in the new, which makes a `StarStrongTailLift`
binder weaker than the corresponding `StarStrongAsymptoticLift` one --- and a
consumer of the new lift a stronger theorem than the same consumer of the old.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section TailNull

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- **Vanishing in the reduced product.**  For every `ε`, all late members of
the family are below `ε` at all late coordinates. -/
def TailNull (X : ℕ → StarStrong.BoundedStarSequence A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ᶠ n in atTop, ‖X t n‖ ≤ ε

/-- **A defect vanishing in the sup norm vanishes in the tail.**  This is the
only comparison between the two vocabularies, and it goes one way. -/
theorem tailNull_of_tendsto_norm {X : ℕ → StarStrong.BoundedStarSequence A}
    (h : Tendsto (fun t ↦ ‖X t‖) atTop (𝓝 0)) : TailNull X := by
  intro ε hε
  have ht : ∀ᶠ t in atTop, ‖X t‖ < ε := h (Iio_mem_nhds hε)
  refine ht.mono fun t htt ↦ Eventually.of_forall fun n ↦ ?_
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (X t) n).trans htt.le

/-- Domination transfers tail vanishing. -/
theorem TailNull.mono {X Y : ℕ → StarStrong.BoundedStarSequence A}
    (hX : TailNull X) (h : ∀ t n, ‖Y t n‖ ≤ ‖X t n‖) : TailNull Y := by
  intro ε hε
  exact (hX ε hε).mono fun t ht ↦ ht.mono fun n hn ↦ (h t n).trans hn

/-- **What a consumer reads off a tail-vanishing family**: past any stage there
is a later member all of whose late coordinates are small.  This is the form the
diagonal selection of `Analysis/ShulmanFillNormingAsymptoticMF` needs, since it
chooses both a member and a coordinate; the coordinate threshold is produced
here rather than prescribed, which is exactly the difference from the sup-norm
vocabulary. -/
theorem TailNull.exists_stage {X : ℕ → StarStrong.BoundedStarSequence A}
    (hX : TailNull X) {ε : ℝ} (hε : 0 < ε) (t₀ : ℕ) :
    ∃ t ≥ t₀, ∃ N : ℕ, ∀ n ≥ N, ‖X t n‖ ≤ ε := by
  obtain ⟨t, htail, ht₀⟩ := ((hX ε hε).and (eventually_ge_atTop t₀)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  exact ⟨t, ht₀, N, hN⟩

end TailNull

section TailLift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
variable [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
variable {B : Type v} [CStarAlgebra B]

/-- **A discrete asymptotic homomorphism into `𝒟` lifting `π`, in the reduced
product.**

Three clauses differ from `StarStrongAsymptoticLift`.  The five defects are
`TailNull` rather than null in the sup norm, so no fixed coordinate is
constrained; and the lift clause is the paper's, `q ∘ φ_t → π` pointwise, rather
than the exact `q (φ_t b) = π b`.  Contractivity stays in the sup norm, because
it is a bound and not a defect: it is what makes every coordinate a contraction,
which the consumer uses. -/
structure StarStrongTailLift (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  /-- The maps of the family. -/
  toFun : ℕ → B → StarStrong.BoundedStarSequence A
  /-- Every value converges `*`-strongly, that is, lies in `𝒟`. -/
  mem : ∀ t b, toFun t b ∈ StarStrong.starStrongSubalgebra ι hnorm hone
  /-- The maps are contractive. -/
  norm_le : ∀ t b, ‖toFun t b‖ ≤ ‖b‖
  /-- The additivity defect vanishes in the tail. -/
  tail_add : ∀ b c, TailNull (fun t ↦ toFun t (b + c) - toFun t b - toFun t c)
  /-- The homogeneity defect vanishes in the tail. -/
  tail_smul : ∀ (z : ℂ) (b : B), TailNull (fun t ↦ toFun t (z • b) - z • toFun t b)
  /-- The multiplicativity defect vanishes in the tail. -/
  tail_mul : ∀ b c, TailNull (fun t ↦ toFun t (b * c) - toFun t b * toFun t c)
  /-- The adjoint defect vanishes in the tail. -/
  tail_star : ∀ b, TailNull (fun t ↦ toFun t (star b) - star (toFun t b))
  /-- The unit defect vanishes in the tail. -/
  tail_one : TailNull (fun t ↦ toFun t 1 - 1)
  /-- The family lifts `π` in the limit. -/
  tendsto_lift : ∀ b, Tendsto (fun t ↦ ‖StarStrong.starStrongLimitHom ι hnorm hone
    ⟨toFun t b, mem t b⟩ - π b‖) atTop (𝓝 0)

namespace StarStrongAsymptoticLift

variable {ι hnorm hone}
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- **Every asymptotic lift is a tail lift.**  Both weakenings are comparisons
in the same direction, so the new binder asks for less than the old one and
every consumer of the new is a stronger theorem. -/
def toTail (φ : StarStrongAsymptoticLift ι hnorm hone π) :
    StarStrongTailLift ι hnorm hone π where
  toFun := φ.toFun
  mem := φ.mem
  norm_le := φ.norm_le
  tail_add b c := tailNull_of_tendsto_norm (φ.tendsto_add b c)
  tail_smul z b := tailNull_of_tendsto_norm (φ.tendsto_smul z b)
  tail_mul b c := tailNull_of_tendsto_norm (φ.tendsto_mul b c)
  tail_star b := tailNull_of_tendsto_norm (φ.tendsto_star b)
  tail_one := tailNull_of_tendsto_norm φ.tendsto_one
  tendsto_lift b := by
    have hz : (fun t ↦ ‖StarStrong.starStrongLimitHom ι hnorm hone
        ⟨φ.toFun t b, φ.mem t b⟩ - π b‖) = fun _ : ℕ ↦ (0 : ℝ) := by
      funext t
      rw [φ.lift t b, sub_self, norm_zero]
    rw [hz]
    exact tendsto_const_nhds

end StarStrongAsymptoticLift

end TailLift

end

end ShulmanFill
end GroupApproximation
