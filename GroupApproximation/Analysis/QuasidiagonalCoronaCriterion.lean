import GroupApproximation.Analysis.KirchbergRordamCorona
import GroupApproximation.Analysis.QuasidiagonalTrace

/-!
# Quasidiagonality of a trace, from a homomorphism into the corona

What the Tikuisis--White--Winter argument actually produces, at the end of its
run through the Kirchberg--Rørdam corona theory, is not a sequence of matrix
models with small multiplicative defect.  It is an **exact algebraic
statement**: a unital `⋆`-homomorphism from `A` into the corona
`Q = ℓ∞(M_{kₙ})/c₀(M_{kₙ})`, together with a lift of it to unital completely
positive maps `A → M_{kₙ}` and a trace condition.

This file proves that this is enough --- that such a corona homomorphism *is*
a quasidiagonal trace.  Nothing here is assumed: the passage from the exact
statement in `Q` back to the asymptotic statement in the matrix algebras is
`KirchbergRordam.tendsto_norm_sub_mul_of_corona_mul`, which is the definition
of the quotient unwound, and the remaining four clauses of
`QuasidiagonalTraceModel` are carried across unchanged.

## Why this is the right interface

It moves the last step of the Annals proof out of the citation.  A statement of
the form "there exist matrix models whose defect tends to zero" and a statement
of the form "there is a `⋆`-homomorphism into `Q` that lifts" are equivalent,
but only the second is what a corona argument produces, and only the first is
what `QuasidiagonalTraceModel` asks for.  With `CoronaModel` in hand, an input
asserting Tikuisis--White--Winter can be stated in the *corona* form it is
proved in --- see `Analysis.TikuisisWhiteWinterDerivation` --- and the
translation is a theorem rather than part of the assumption.

## The packaging of the sequence

The multiplicativity clause has to name the element of `ℓ∞` that the models
assemble into, and membership in `ℓ∞` needs a bound.  Rather than carry a
`Memℓp` proof inside the structure --- which would make the structure depend
on which bound was chosen --- the assembled sequence is a *field*, `seq`, tied
to the models by `seq_apply`.  Any bound whatsoever produces the same
structure, and the criterion below reads the models only through
`seq_apply`.

The `Nonempty` hypothesis on the models is a parameter of the structure rather
than a field, because the corona's C⋆-structure is stated over it and a field
would not be in scope in the types of later fields.  It costs nothing:
`ShulmanTrace.MFTraceModel.exists_shift` records that the trace clause at the
unit already forces all but finitely many models to be nonempty.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix KirchbergRordam
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **A corona model for a trace**: unital completely positive matrix models
whose induced map into `ℓ∞/c₀` is *multiplicative on the nose*, together with
the convergence of their normalized traces.

The difference from `QuasidiagonalTraceModel` is exactly the multiplicativity
clause: there it is asymptotic in the operator norm, here it is exact in the
corona.  `isQuasidiagonalTrace_of_coronaModel` proves the two agree. -/
structure CoronaModel (τ : A → ℂ) (space : ℕ → FiniteModel)
    [∀ n, Nonempty (space n)] where
  /-- The maps `φₙ : A → M_{kₙ}`, genuinely `ℂ`-linear. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φₙ` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φₙ` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- The models, assembled into a bounded sequence. -/
  seq : A → BoundedMatrixSequence (fun n => (space n).carrier)
  /-- The assembly is the models. -/
  seq_apply : ∀ (a : A) (n : ℕ), seq a n = map n a
  /-- **The map into the corona is multiplicative.** -/
  corona_mul : ∀ a b : A,
    normMatrixCStarCoronaMk (fun n => (space n).carrier) (seq a)
        * normMatrixCStarCoronaMk (fun n => (space n).carrier) (seq b)
      = normMatrixCStarCoronaMk (fun n => (space n).carrier) (seq (a * b))
  /-- The normalized traces of the models converge to `τ`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n => ‖τ a - normTrace (space n) (map n a)‖) atTop (nhds 0)

/-- **A corona model is a quasidiagonal-trace model.**

The only clause that changes is multiplicativity, and it changes by the
definition of the corona: a product identity in `ℓ∞/c₀` says precisely that
the defect sequence is null, which is the asymptotic multiplicativity
`QuasidiagonalTraceModel` asks for.

This is the last step of the Tikuisis--White--Winter argument, proved. -/
def CoronaModel.toQuasidiagonalTraceModel {τ : A → ℂ} {space : ℕ → FiniteModel}
    [∀ n, Nonempty (space n)] (M : CoronaModel τ space) :
    QuasidiagonalTraceModel τ where
  space := space
  map := M.map
  map_one := M.map_one
  completelyPositive := M.completelyPositive
  tendsto_mul a b := by
    have h := KirchbergRordam.tendsto_norm_sub_mul_of_corona_mul
      (X := fun n => (space n).carrier) (u := M.seq a) (v := M.seq b)
      (w := M.seq (a * b)) (M.corona_mul a b)
    refine h.congr fun n => ?_
    rw [M.seq_apply, M.seq_apply, M.seq_apply]
  tendsto_trace := M.tendsto_trace

/-- The proposition-level form: a trace with a corona model is
quasidiagonal. -/
theorem isQuasidiagonalTrace_of_coronaModel {τ : A → ℂ}
    {space : ℕ → FiniteModel} [∀ n, Nonempty (space n)]
    (M : CoronaModel τ space) : IsQuasidiagonalTrace τ :=
  ⟨M.toQuasidiagonalTraceModel⟩

/-- **The existential form**, which is the shape an input asserting
Tikuisis--White--Winter in its corona formulation takes. -/
def HasCoronaModel (τ : A → ℂ) : Prop :=
  ∃ (space : ℕ → FiniteModel) (hne : ∀ n, Nonempty (space n)),
    Nonempty (@CoronaModel A _ τ space hne)

theorem isQuasidiagonalTrace_of_hasCoronaModel {τ : A → ℂ}
    (h : HasCoronaModel τ) : IsQuasidiagonalTrace τ := by
  obtain ⟨space, hne, ⟨M⟩⟩ := h
  exact @isQuasidiagonalTrace_of_coronaModel A _ τ space hne M

end

end Quasidiagonal
end GroupApproximation
