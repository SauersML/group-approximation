import GroupApproximation.Analysis.PrintedLiftingSteps
import GroupApproximation.Sofic.OpAlmostRepresentation

/-!
# A corona representation lifts to an almost representation

Proof-ledger row `CO.04`.  The printed proof of `thm:projection-collapse`
opens its analytic half with

> Choose unitary coordinate lifts `U_n(h)` of `Θ(h)` (Lemma
> \ref{lem:unitarycorona}).

Everything downstream of that sentence is now in the corpus and is stated for
an `OpAlmostRepresentation` — the cocycle
(`CollapseLambdaCocycle.lambda_cocycle_almost`), the compression bundle
(`Sofic/OmegaKazhdanCompression.omegaCompressionRep`), the identification of
the two representations (`CollapseRouteJoin`) and the contradiction
(`CollapseCompressionBundle.collapse_contradiction_printed`).  What was
missing is the sentence itself: the passage from a homomorphism
`Θ : E →* 𝓤(𝒬)` into the corona's unitary group to an almost representation.

`coronaAlmostRep` is that passage, and `unitarySequenceToCorona_surjective` is
`lem:unitarycorona` in the form it needs.

## Why the lift is only asymptotically multiplicative, and why that is enough

A choice of unitary lift is made independently at each group element, so
`U(gh)` and `U(g)U(h)` are two lifts of the same corona unitary rather than
the same sequence.  They therefore differ by a sequence that is null in
operator norm along `cofinite`, which is exactly the defect condition an
`OpAlmostRepresentation` records — and on `ℕ` the cofinite filter *is*
`atTop`, so the `∃ N, ∀ n ≥ N` form the structure asks for is the same
statement.  No estimate is lost and none is needed: the defect is not small,
it vanishes.

`PrintedLiftingSteps.exists_boundedLift_polarPatch` supplies the lift without
passing through the unitary-sequence corona: it exposes the patched
coordinatewise unitary sequence directly, together with the fact that its
class is the given unitary.
-/

namespace GroupApproximation
namespace CollapseUnitaryLift

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-! ## `lem:unitarycorona`, in sequence form -/

/-- **Every unitary of the corona is the class of a coordinatewise unitary
sequence.**  This is `lem:unitarycorona`; the polar-corrected patched sequence
of `PrintedLiftingSteps` is the witness. -/
theorem unitarySequenceToCorona_surjective :
    Function.Surjective (unitarySequenceToCorona X) := by
  intro x
  obtain ⟨a, _, _, hpatch⟩ :=
    PrintedLiftingSteps.exists_boundedLift_polarPatch X x
  exact ⟨PrintedLiftingSteps.polarPatch X a, hpatch⟩

/-! ## The chosen lift -/

variable {E : Type} [Group E]
  (Θ : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))

/-- A chosen coordinatewise unitary lift of `Θ(g)`, one for each `g`. -/
def liftFam (g : E) : ∀ n, Matrix.unitaryGroup (X n) ℂ :=
  Classical.choose (unitarySequenceToCorona_surjective X (Θ g))

theorem unitarySequenceToCorona_liftFam (g : E) :
    unitarySequenceToCorona X (liftFam X Θ g) = Θ g :=
  Classical.choose_spec (unitarySequenceToCorona_surjective X (Θ g))

/-- The two lifts of `Θ(gh)` — the chosen one, and the product of the chosen
lifts of `Θ(g)` and `Θ(h)` — have the same class, because `Θ` is a
homomorphism and `unitarySequenceToCorona` is one. -/
theorem liftFam_mul_class (g h : E) :
    unitarySequenceToCorona X (liftFam X Θ (g * h))
      = unitarySequenceToCorona X (liftFam X Θ g * liftFam X Θ h) := by
  calc unitarySequenceToCorona X (liftFam X Θ (g * h))
      = Θ (g * h) := unitarySequenceToCorona_liftFam X Θ (g * h)
    _ = Θ g * Θ h := map_mul Θ g h
    _ = unitarySequenceToCorona X (liftFam X Θ g) *
          unitarySequenceToCorona X (liftFam X Θ h) := by
        rw [unitarySequenceToCorona_liftFam, unitarySequenceToCorona_liftFam]
    _ = unitarySequenceToCorona X (liftFam X Θ g * liftFam X Θ h) :=
        (map_mul (unitarySequenceToCorona X) _ _).symm

/-- The coordinates of the multiplicative defect of the chosen lift. -/
theorem coord_defect (g h : E) (n : ℕ) :
    ((unitarySequenceBounded X (liftFam X Θ (g * h))
        - unitarySequenceBounded X (liftFam X Θ g * liftFam X Θ h)) n
      : Matrix (X n) (X n) ℂ)
      = ((liftFam X Θ (g * h) n : Matrix (X n) (X n) ℂ))
        - (liftFam X Θ g n : Matrix (X n) (X n) ℂ) *
          (liftFam X Θ h n : Matrix (X n) (X n) ℂ) := rfl

/-- **The multiplicative defect of the chosen lift vanishes.**  The two lifts
of `Θ(gh)` differ by a sequence whose class in the corona is zero. -/
theorem tendsto_defect (g h : E) :
    Tendsto (fun n ↦ ‖((liftFam X Θ (g * h) n : Matrix (X n) (X n) ℂ))
        - (liftFam X Θ g n : Matrix (X n) (X n) ℂ) *
          (liftFam X Θ h n : Matrix (X n) (X n) ℂ)‖)
      cofinite (nhds 0) := by
  have hcorona : normMatrixCStarCoronaMk (fun n ↦ X n)
      (unitarySequenceBounded X (liftFam X Θ (g * h))
        - unitarySequenceBounded X (liftFam X Θ g * liftFam X Θ h)) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg
      (fun t : unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        (t : NormMatrixCStarCorona (fun n ↦ X n)))
      (liftFam_mul_class X Θ g h)
  have hnull := (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hcorona
  exact hnull

/-! ## The almost representation -/

/-- **The printed *"choose unitary coordinate lifts `U_n(h)` of `Θ(h)`"*.**

A homomorphism into the unitary group of the corona induces an operator-norm
almost representation on the same models.  The lift is chosen independently at
each group element, so it is multiplicative only up to a defect — and that
defect vanishes, because the two lifts of `Θ(gh)` are lifts of the same corona
unitary.  On `ℕ` the cofinite filter is `atTop`, so the vanishing is already
in the `∃ N, ∀ n ≥ N` form the structure records. -/
def coronaAlmostRep : OpAlmostRepresentation E where
  model := X
  modelNonempty _ := Fintype.card_pos
  map n g := liftFam X Θ g n
  asymptoticallyMultiplicative g h ε hε := by
    have hev : ∀ᶠ n in cofinite,
        ‖((liftFam X Θ (g * h) n : Matrix (X n) (X n) ℂ))
          - (liftFam X Θ g n : Matrix (X n) (X n) ℂ) *
            (liftFam X Θ h n : Matrix (X n) (X n) ℂ)‖ ≤ ε := by
      filter_upwards
        [(Metric.tendsto_nhds.mp (tendsto_defect X Θ g h)) ε hε] with n hn
      rw [Real.dist_eq, sub_zero, abs_norm] at hn
      exact hn.le
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
    exact hev

@[simp] theorem coronaAlmostRep_model : (coronaAlmostRep X Θ).model = X := rfl

@[simp] theorem coronaAlmostRep_map (n : ℕ) (g : E) :
    (coronaAlmostRep X Θ).map n g = liftFam X Θ g n := rfl

end

end CollapseUnitaryLift
end GroupApproximation
