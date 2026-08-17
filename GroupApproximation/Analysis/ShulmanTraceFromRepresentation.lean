import GroupApproximation.Analysis.ShulmanTraceFactorization

/-!
# Sequential models from a representation into the `atTop` tracial quotient

Everything a `⋆`-homomorphism into a tracial matrix quotient gives you towards
Shulman's sequential definition, which is four of the five clauses, with the
fifth isolated as the single remaining obligation.

## Why the ideal is at `atTop`

`TracialMatrixQuotient X l` is filter-generic: its ring, star and normed
structure are all stated for an arbitrary `l : Filter ℕ`.  Taking `l = atTop`
— the ideal `⊕₂ M_{kₙ}` of sequences that are `‖·‖₂`-null in the ordinary
sense — makes membership in the ideal *literally* the sequential defect
clause.  Nothing has to be extracted, and the clauses hold for **all** pairs
`a, b`, not merely for a countable family:

```text
Φ(ab) = Φ(a)Φ(b) in the quotient  ⟺  ‖rep(ab)ₙ − rep(a)ₙ rep(b)ₙ‖₂ → 0
```

At an ultrafilter this equivalence is with `limω` instead, which is why the
ultrafilter version cannot feed the sequential definition: an `ω`-limit
constrains no particular subsequence, so reindexing fixes only the countable
family the subsequence was extracted against.

## Why per-element representatives, and why non-linearity is harmless

`rep` is chosen separately for each `a`, through the quotient-norm infimum:
`‖rep a‖ < ‖Φ a‖ + 1`.  It is *not* linear, and it does not need to be — the
model maps `φₙ` in Shulman's definition carry no structure obligation at all.
The linearity clause still comes out, because `rep(c₁a + c₂b) − c₁rep(a) −
c₂rep(b)` represents `c₁Φ(a) + c₂Φ(b) − c₁Φ(a) − c₂Φ(b) = 0` in the quotient,
hence lies in the ideal, hence is `‖·‖₂`-null.  The same argument gives the
multiplicativity and `⋆` clauses.  What the norm control buys is the
boundedness clause outright, and the legality of an `ε/3` argument for the
trace clause downstream: `|tr x| ≤ ‖x‖ ≤ ‖rep a‖ ≤ ‖Φ a‖ + 1`, so the
coordinate traces are equicontinuous in `a` up to an `o(1)` even though `rep`
is not linear.

Contrast with `ShulmanTraceFactorization`, which lifts along a ℂ-Hamel basis
and so gets *exact* linearity but no norm control, hence no `ε/3` and no way
across a dense subspace.  Bounded-per-element beats linear here.

## What is left

`modelOfRepresentation` takes the trace clause as an argument and returns a
full `TraceApproximationModel`.  That is deliberate: the trace clause is the
one thing a representation does not supply, because the natural trace on the
quotient is an ultralimit while the sequential definition asks for an ordinary
one.  It is supplied downstream, where the trace values on a dense set are
known along `atTop` for an independent reason.  No declaration here assumes
it.
-/

open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation
namespace ShulmanTrace

open TracialUltraproduct

/- Same budget as `TracialMatrixUltraproduct`: typeclass search on the ideal
quotient has to unfold `lp` and rediscover the `FiniteModel` projections. -/
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {l : Filter ℕ}

/-! ## Representatives of nearly minimal norm -/

/-- Every class has a representative of nearly minimal norm.  This is the
quotient-norm infimum, and it is the only place norm control enters. -/
theorem exists_rep_norm_lt (x : TracialMatrixQuotient X l) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : ModelBoundedSequence X,
      tracialMatrixQuotientMk X l p = x ∧ ‖p‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- A per-element bounded representative of `Φ a`.  Chosen, not constructed:
`rep` is deliberately allowed to be non-linear. -/
def qrep (Φ : A → TracialMatrixQuotient X l) (a : A) : ModelBoundedSequence X :=
  Classical.choose (exists_rep_norm_lt (Φ a) one_pos)

@[simp] theorem qrep_mk (Φ : A → TracialMatrixQuotient X l) (a : A) :
    tracialMatrixQuotientMk X l (qrep Φ a) = Φ a :=
  (Classical.choose_spec (exists_rep_norm_lt (Φ a) one_pos)).1

/-- The norm control that makes the downstream `ε/3` argument legal. -/
theorem qrep_norm_lt (Φ : A → TracialMatrixQuotient X l) (a : A) :
    ‖qrep Φ a‖ < ‖Φ a‖ + 1 :=
  (Classical.choose_spec (exists_rep_norm_lt (Φ a) one_pos)).2

theorem qrep_coord_norm_le (Φ : A → TracialMatrixQuotient X l) (a : A)
    (n : ℕ) : ‖qrep Φ a n‖ ≤ ‖qrep Φ a‖ :=
  boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (qrep Φ a) n

/-! ## The three defect clauses, as ideal membership

Each is the same two lines: the quotient map kills the defect, so the defect
is in the ideal, and at `l = atTop` being in the ideal *is* the clause. -/

/-- Multiplicativity. -/
theorem isHilbertSchmidtNull_qrep_mul {Φ : A → TracialMatrixQuotient X l}
    (hmul : ∀ a b : A, Φ (a * b) = Φ a * Φ b) (a b : A) :
    IsHilbertSchmidtNull X l (qrep Φ (a * b) - qrep Φ a * qrep Φ b) := by
  have hmk : tracialMatrixQuotientMk X l (qrep Φ a * qrep Φ b)
      = tracialMatrixQuotientMk X l (qrep Φ a) *
        tracialMatrixQuotientMk X l (qrep Φ b) :=
    _root_.map_mul (tracialMatrixQuotientMk X l) (qrep Φ a) (qrep Φ b)
  refine (tracialMatrixQuotientMk_eq_zero_iff X l _).mp ?_
  rw [_root_.map_sub, hmk, qrep_mk, qrep_mk, qrep_mk, hmul]
  exact sub_self _

/-- `⋆`-compatibility. -/
theorem isHilbertSchmidtNull_qrep_star {Φ : A → TracialMatrixQuotient X l}
    (hstar : ∀ a : A, Φ (star a) = star (Φ a)) (a : A) :
    IsHilbertSchmidtNull X l (qrep Φ (star a) - star (qrep Φ a)) := by
  have hst : tracialMatrixQuotientMk X l (star (qrep Φ a))
      = star (tracialMatrixQuotientMk X l (qrep Φ a)) :=
    (tracialMatrixQuotient_star_mk X l (qrep Φ a)).symm
  refine (tracialMatrixQuotientMk_eq_zero_iff X l _).mp ?_
  rw [_root_.map_sub, hst, qrep_mk, qrep_mk, hstar]
  exact sub_self _

/-- Linearity.  This is the clause the Hamel lift got exactly and this one
gets only up to the ideal — which is all the definition asks for. -/
theorem isHilbertSchmidtNull_qrep_linear {Φ : A → TracialMatrixQuotient X l}
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a)
    (c₁ c₂ : ℂ) (a b : A) :
    IsHilbertSchmidtNull X l
      (qrep Φ (c₁ • a + c₂ • b) - c₁ • qrep Φ a - c₂ • qrep Φ b) := by
  have hs₁ : tracialMatrixQuotientMk X l (c₁ • qrep Φ a)
      = c₁ • tracialMatrixQuotientMk X l (qrep Φ a) :=
    (smul_tracialMatrixQuotientMk c₁ (qrep Φ a)).symm
  have hs₂ : tracialMatrixQuotientMk X l (c₂ • qrep Φ b)
      = c₂ • tracialMatrixQuotientMk X l (qrep Φ b) :=
    (smul_tracialMatrixQuotientMk c₂ (qrep Φ b)).symm
  refine (tracialMatrixQuotientMk_eq_zero_iff X l _).mp ?_
  simp only [_root_.map_sub]
  rw [hs₁, hs₂, qrep_mk, qrep_mk, qrep_mk, hadd, hsmul, hsmul]
  abel

/-! ## The model, with the trace clause as the single argument -/

/-- **Four clauses for free.**  A `⋆`-homomorphism into the tracial quotient
supplies asymptotic multiplicativity, linearity, `⋆`-compatibility and the
uniform bound; the trace clause is the argument `htrace`, because a
representation does not determine it.

At `l = atTop` the conclusion is a model in Shulman's sequential sense. -/
def modelOfRepresentation {τ : A → ℂ} (Φ : A → TracialMatrixQuotient X l)
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a)
    (hmul : ∀ a b : A, Φ (a * b) = Φ a * Φ b)
    (hstar : ∀ a : A, Φ (star a) = star (Φ a))
    (htrace : ∀ a : A,
      Tendsto (fun n ↦ ‖τ a - normTrace (X n) (qrep Φ a n)‖) l (nhds 0)) :
    TraceApproximationModel l (fun Y B ↦ hsNorm Y B) τ where
  space := X
  map := fun n a ↦ qrep Φ a n
  tendsto_mul a b := isHilbertSchmidtNull_qrep_mul hmul a b
  tendsto_linear c₁ c₂ a b := isHilbertSchmidtNull_qrep_linear hadd hsmul c₁ c₂ a b
  tendsto_star a := by
    have hnull : Tendsto (fun n ↦ hsNorm (X n)
        ((qrep Φ (star a) - star (qrep Φ a)) n)) l (nhds 0) :=
      isHilbertSchmidtNull_qrep_star hstar a
    refine hnull.congr fun n ↦ ?_
    show hsNorm (X n) (qrep Φ (star a) n - star (qrep Φ a n))
      = hsNorm (X n) (qrep Φ (star a) n - (qrep Φ a n)ᴴ)
    rw [Matrix.star_eq_conjTranspose]
  bounded a := ⟨‖qrep Φ a‖, fun n ↦ qrep_coord_norm_le Φ a n⟩
  tendsto_trace := htrace

/-- **The sequential predicate from a representation.**  At `atTop` the four
free clauses are exactly Shulman's, so a representation whose coordinate
traces converge to `τ` in the ordinary sense makes `τ` hyperlinear.

This is the shape the sofic route consumes: soficity supplies `atTop`
convergence of the coordinate traces on the group unitaries with no
ultrafilter anywhere, and the norm control above carries it to the whole
algebra. -/
theorem isHyperlinearTrace_of_representation {τ : A → ℂ}
    (Φ : A → TracialMatrixQuotient X atTop)
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a)
    (hmul : ∀ a b : A, Φ (a * b) = Φ a * Φ b)
    (hstar : ∀ a : A, Φ (star a) = star (Φ a))
    (htrace : ∀ a : A,
      Tendsto (fun n ↦ ‖τ a - normTrace (X n) (qrep Φ a n)‖) atTop (nhds 0)) :
    IsHyperlinearTrace τ :=
  ⟨modelOfRepresentation Φ hadd hsmul hmul hstar htrace⟩

end

end ShulmanTrace
end GroupApproximation
