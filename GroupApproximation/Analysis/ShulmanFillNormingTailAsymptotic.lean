import GroupApproximation.Analysis.ShulmanFillNormingAsymptotic

/-!
# Asymptotic lifts whose defects are measured beyond a moving cut

`ShulmanFill.StarStrongAsymptoticLift` measures its five defects in the norm of
`StarStrong.BoundedStarSequence A`, which is `lp _ ∞` and therefore the supremum
over all coordinates.  `Analysis/ShulmanFillNormingPrintedPairCharacter` shows
that this is too strong at finite-dimensional coefficients: a supremum bounds
every fixed coordinate, so `(φ_t ·)ₙ` is an asymptotic homomorphism into `A n`
for each fixed `n`, and when `A n` is finite-dimensional its limit along an
ultrafilter is an honest unital `*`-homomorphism.  At the printed models that is
a character on `B`, and `B(ℂ²)` has none.

The `*`-strong limit map cannot see finitely many coordinates, so nothing
downstream wants the supremum.  This module records the vocabulary the repair
needs.

## The moving cut

A lift carries a function `cut : ℕ → ℕ` and its defects are required to be small
only at coordinates `n ≥ cut t`.  The cut is *data*, quantified existentially
wherever a lift is asked for, and it is what the character argument has nothing
to bite on: with `cut t` growing, coordinate `0` is constrained by no defect at
all.

Two forms were possible and only this one supports the consumer.  Asking merely
that each defect vanish in the tail --- for every `ε`, eventually in `t`,
eventually in `n` --- lets the coordinate threshold depend on the pair `(b, c)`
whose defect is being measured, and the diagonal selection of
`Analysis/ShulmanFillNormingAsymptoticMF` must choose its coordinate before any
pair is in hand.  With one cut serving every pair, `TailNull.tendsto_diag` turns
a selection past the cut into exactly the vanishing the old proof consumed, so
the consumer's argument survives unchanged in shape.

`tailNull_of_tendsto_norm` is the comparison with the old vocabulary: a defect
vanishing in the sup norm vanishes past every cut.  So
`StarStrongAsymptoticLift.toTail` turns every lift in the old vocabulary into
one in the new, with the zero cut; a `StarStrongTailLift` binder therefore asks
for strictly less than a `StarStrongAsymptoticLift` one, and every consumer
re-proved against it is a stronger theorem.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section TailNull

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]

/-- **Vanishing beyond a moving cut.**  For every `ε`, all late members of the
family are below `ε` at every coordinate past their own cut. -/
def TailNull (cut : ℕ → ℕ) (X : ℕ → StarStrong.BoundedStarSequence A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ n, cut t ≤ n → ‖X t n‖ ≤ ε

/-- **A defect vanishing in the sup norm vanishes past every cut.**  This is the
only comparison between the two vocabularies, and it goes one way. -/
theorem tailNull_of_tendsto_norm (cut : ℕ → ℕ)
    {X : ℕ → StarStrong.BoundedStarSequence A}
    (h : Tendsto (fun t ↦ ‖X t‖) atTop (𝓝 0)) : TailNull cut X := by
  intro ε hε
  have ht : ∀ᶠ t in atTop, ‖X t‖ < ε := h (Iio_mem_nhds hε)
  refine ht.mono fun t htt n _ ↦ ?_
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (X t) n).trans htt.le

/-- Domination transfers tail vanishing. -/
theorem TailNull.mono {cut : ℕ → ℕ} {X Y : ℕ → StarStrong.BoundedStarSequence A}
    (hX : TailNull cut X) (h : ∀ t n, ‖Y t n‖ ≤ ‖X t n‖) : TailNull cut Y := by
  intro ε hε
  exact (hX ε hε).mono fun t ht n hn ↦ (h t n).trans (ht n hn)

/-- **What the consumer reads off a tail-vanishing family.**  A selection of
coordinates past the cut turns tail vanishing into vanishing of the diagonal,
which is the hypothesis the reduced-product transfer lemma of
`Analysis/ShulmanFillNormingAsymptoticMF` consumes.  This is the whole reason
the cut is one function rather than one per pair. -/
theorem TailNull.tendsto_diag {cut nsel : ℕ → ℕ}
    {X : ℕ → StarStrong.BoundedStarSequence A} (hX : TailNull cut X)
    (hsel : ∀ m, cut m ≤ nsel m) :
    Tendsto (fun m ↦ ‖X m (nsel m)‖) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hX (ε / 2) (by linarith))
  refine ⟨T, fun m hm ↦ ?_⟩
  have hbound := hT m hm (nsel m) (hsel m)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

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

/-- **A discrete asymptotic homomorphism into `𝒟` lifting `π`, with its defects
measured past a moving cut.**

Three clauses differ from `StarStrongAsymptoticLift`.  The five defects are
`TailNull cut` rather than null in the sup norm, so no fixed coordinate is
constrained once the cut grows; the cut is carried as data, so a consumer asking
for a lift quantifies over it existentially; and the lift clause is the paper's
pointwise `q ∘ φ_t → π` rather than the exact `q (φ_t b) = π b`.

Contractivity stays in the sup norm, deliberately: it is a bound and not a
defect, and it is what makes every coordinate a contraction, which the consumer
uses. -/
structure StarStrongTailLift (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  /-- The maps of the family. -/
  toFun : ℕ → B → StarStrong.BoundedStarSequence A
  /-- The coordinate past which the defects are controlled. -/
  cut : ℕ → ℕ
  /-- Every value converges `*`-strongly, that is, lies in `𝒟`. -/
  mem : ∀ t b, toFun t b ∈ StarStrong.starStrongSubalgebra ι hnorm hone
  /-- The maps are contractive. -/
  norm_le : ∀ t b, ‖toFun t b‖ ≤ ‖b‖
  /-- The additivity defect vanishes past the cut. -/
  tail_add : ∀ b c, TailNull cut (fun t ↦ toFun t (b + c) - toFun t b - toFun t c)
  /-- The homogeneity defect vanishes past the cut. -/
  tail_smul : ∀ (z : ℂ) (b : B),
    TailNull cut (fun t ↦ toFun t (z • b) - z • toFun t b)
  /-- The multiplicativity defect vanishes past the cut. -/
  tail_mul : ∀ b c, TailNull cut (fun t ↦ toFun t (b * c) - toFun t b * toFun t c)
  /-- The adjoint defect vanishes past the cut. -/
  tail_star : ∀ b, TailNull cut (fun t ↦ toFun t (star b) - star (toFun t b))
  /-- The unit defect vanishes past the cut. -/
  tail_one : TailNull cut (fun t ↦ toFun t 1 - 1)
  /-- The family lifts `π` in the limit. -/
  tendsto_lift : ∀ b, Tendsto (fun t ↦ ‖StarStrong.starStrongLimitHom ι hnorm hone
    ⟨toFun t b, mem t b⟩ - π b‖) atTop (𝓝 0)

namespace StarStrongAsymptoticLift

variable {ι hnorm hone}
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- **Every asymptotic lift is a tail lift**, with the zero cut.  All three
weakenings run the same way, so the new binder asks for less than the old one
and every consumer of the new is a stronger theorem. -/
def toTail (φ : StarStrongAsymptoticLift ι hnorm hone π) :
    StarStrongTailLift ι hnorm hone π where
  toFun := φ.toFun
  cut := fun _ ↦ 0
  mem := φ.mem
  norm_le := φ.norm_le
  tail_add b c := tailNull_of_tendsto_norm _ (φ.tendsto_add b c)
  tail_smul z b := tailNull_of_tendsto_norm _ (φ.tendsto_smul z b)
  tail_mul b c := tailNull_of_tendsto_norm _ (φ.tendsto_mul b c)
  tail_star b := tailNull_of_tendsto_norm _ (φ.tendsto_star b)
  tail_one := tailNull_of_tendsto_norm _ φ.tendsto_one
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
