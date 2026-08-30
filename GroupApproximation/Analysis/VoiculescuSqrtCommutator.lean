import GroupApproximation.Analysis.VoiculescuSpectralOrderBridge
import GroupApproximation.Analysis.ShulmanCoronaSquareRootCommutator

/-!
# Square roots commute asymptotically, at the order the algebra already has

`ShulmanCoronaSquareRoot.isNull_commutator_sqrtSequence` proves that a bounded
positive sequence with null commutators keeps them null after coordinatewise
square roots.  It is stated over `CStarAlgebra.spectralOrder`, because a general
C⋆-algebra carries no order of its own and the square root needs one.

Every algebra Voiculescu's construction actually uses — `B(H)` above all — does
carry an order, and `CFC.sqrt` at *that* order is the square root the
construction writes down: `improveUnit e f = e + √(1-e) f √(1-e)` in
`VoiculescuMonotoneStep` is a `B(H)` expression through and through.  The two
square roots are not definitionally the same term, so the corona lemma does not
apply to it as stated.

`spectralOrder_eq` says the two orders are the same instance.  This file spends
that equality once and restates the commutator lemma in the form the
construction consumes: ordinary `CFC.sqrt`, ordinary Loewner order, no mention of
the spectral order anywhere in the conclusion.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter PolarLiftingGeneralCStar ShulmanCoronaSquareRoot

universe u

/-! ### Naming the spectral-order square root

Inside this section the spectral order *is* the ambient order, so `0 ≤ x` and
`CFC.sqrt x` mean the spectral-order versions.  Naming them here is what lets
them be mentioned outside, where a different order is ambient. -/

section Spectral

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

variable (A : Type*) [CStarAlgebra A]

/-- Nonnegativity measured in `CStarAlgebra.spectralOrder`. -/
def SpectralNonneg (x : A) : Prop := 0 ≤ x

/-- The square root formed with `CStarAlgebra.spectralOrder`; this is the square
root `ShulmanCoronaSquareRoot.sqrtSequence` takes in each coordinate. -/
noncomputable def spectralSqrt (x : A) : A := CFC.sqrt x

theorem spectralNonneg_spectralSqrt (x : A) : SpectralNonneg A (spectralSqrt A x) :=
  CFC.sqrt_nonneg x

theorem spectralSqrt_mul_self {x : A} (hx : SpectralNonneg A x) :
    spectralSqrt A x * spectralSqrt A x = x :=
  CFC.sqrt_mul_sqrt_self x hx

end Spectral

/-! ### Spending the bridge

Both statements below are the bridge doing its one job.  The second is the
reason the first is worth having: uniqueness of positive square roots is
available at the registered order, and the spectral square root qualifies as
soon as its positivity is read there. -/

section Registered

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Nonnegativity in the spectral order is nonnegativity in the registered order. -/
theorem spectralNonneg_iff (x : A) : SpectralNonneg A x ↔ 0 ≤ x := by
  unfold SpectralNonneg
  rw [spectralOrder_eq A]

/-- The spectral-order square root is the registered-order square root. -/
theorem spectralSqrt_eq_sqrt {x : A} (hx : 0 ≤ x) : spectralSqrt A x = CFC.sqrt x :=
  (CFC.sqrt_unique (spectralSqrt_mul_self A ((spectralNonneg_iff x).2 hx))
    ((spectralNonneg_iff _).1 (spectralNonneg_spectralSqrt A x))).symm

end Registered

/-! ### The commutator lemma at the registered orders -/

section Sequences

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
  [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)] (l : Filter ℕ)

/-- The coordinatewise square root of a bounded positive sequence, with both the
positivity hypothesis and the square roots read in the registered orders. -/
noncomputable def sqrtSequenceReg (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) :
    BoundedCStarSequence A :=
  sqrtSequence A a fun n ↦ (spectralNonneg_iff (a n)).2 (ha n)

omit [∀ n, Nontrivial (A n)] in
@[simp] theorem sqrtSequenceReg_apply
    (a : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    sqrtSequenceReg A a ha n = CFC.sqrt (a n) :=
  spectralSqrt_eq_sqrt (ha n)

/-- The corona square-root lemma, with the registered orders in the hypothesis. -/
theorem isNull_commutator_sqrtSequenceReg
    (a b : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n)
    (hab : IsNullCStarSequence A l (a * b - b * a)) :
    IsNullCStarSequence A l
      (sqrtSequenceReg A a ha * b - b * sqrtSequenceReg A a ha) :=
  isNull_commutator_sqrtSequence A l a b _ hab

/-- **The form the construction consumes.**  A bounded sequence of positive
operators that asymptotically commutes with a bounded sequence keeps that
asymptotic commutation after coordinatewise square roots — with `0 ≤ ·` and
`CFC.sqrt` both read in the registered order of each coordinate algebra. -/
theorem tendsto_norm_commutator_sqrt
    (a b : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n)
    (hab : Tendsto (fun n ↦ ‖a n * b n - b n * a n‖) l (nhds 0)) :
    Tendsto (fun n ↦ ‖CFC.sqrt (a n) * b n - b n * CFC.sqrt (a n)‖) l (nhds 0) := by
  have hab' : IsNullCStarSequence A l (a * b - b * a) :=
    Tendsto.congr (fun n ↦ by simp [lp.infty_coeFn_mul]) hab
  refine Tendsto.congr (fun n ↦ ?_) (isNull_commutator_sqrtSequenceReg A l a b ha hab')
  simp [lp.infty_coeFn_mul]

end Sequences

/-! ### The demonstration at `B(H)`

Nothing in the statement below mentions the spectral order, the corona, or the
bridge.  `CFC.sqrt` is the `B(H)` square root, `0 ≤ ·` is the Loewner order, and
this is exactly the hypothesis the quasicentrality step of the monotone unit
needs about `√(1 - e)`. -/

section BoundedOperators

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] (l : Filter ℕ)

/-- **Square roots inherit asymptotic commutation on `B(H)`.** -/
theorem tendsto_norm_commutator_sqrt_bh
    (a b : BoundedCStarSequence fun _ : ℕ ↦ H →L[ℂ] H) (ha : ∀ n, 0 ≤ a n)
    (hab : Tendsto (fun n ↦ ‖a n * b n - b n * a n‖) l (nhds 0)) :
    Tendsto (fun n ↦ ‖CFC.sqrt (a n) * b n - b n * CFC.sqrt (a n)‖) l (nhds 0) :=
  tendsto_norm_commutator_sqrt _ l a b ha hab

end BoundedOperators

end ShulmanFill
end GroupApproximation
