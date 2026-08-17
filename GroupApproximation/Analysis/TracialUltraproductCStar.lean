import GroupApproximation.Analysis.TracialMatrixUltraproduct

/-!
# The C-star-side obligations of the tracial matrix ultraproduct

`Analysis/MaximalGroupCStarTrace.canonicalMaximalTrace_factorsThrough` takes a
target algebra `B` with `[CStarAlgebra B]` and a trace bundled as a
*continuous* linear functional `B →L[ℂ] ℂ`.  The tracial matrix ultraproduct
of `Analysis/TracialMatrixUltraproduct.lean` is the intended `B`, and this
file supplies the second of those two things.

## What is here

`ultratraceCLM`: the ultratrace as a `→L[ℂ] ℂ`.  The analytic content is
`norm_ultratrace_le`, proved in the ultraproduct file itself; all that is
added here is the bundling, which is what the density argument of
`maximalGroupCStar_ext_of_generator` consumes.  Continuity is not decoration:
two functionals agreeing on the canonical unitaries agree on their linear
span, and only continuity carries that to the closure.

The `example` below is a universe tripwire.  The lift out of `C*(G)` is
universe-relative — `maximalGroupCStar_existsUnique_lift` extends a
representation only into a target in the *same* universe as the group — so the
quotient must stay in `Type 0`.  It does, because `FiniteModel.carrier : Type`
rather than `Type*`, and the `example` fails to elaborate if that ever
changes.

## What is *not* here, and is the one thing blocking the chain

There is still no `CStarAlgebra (TracialMatrixQuotient X ω)` instance, so
`maximalGroupCStar_existsUnique_lift` cannot fire and there is no
`π : C*(G) → Mω` yet.  This is **not** an instance declaration waiting to be
typed out.  The C-star identity for the quotient norm
`‖b + J‖ = inf {‖b + j‖ : j ∈ J}` is a genuine theorem: its standard proof
runs through an approximate unit of `J` and the identity
`‖b + J‖ = lim_λ ‖b - b e_λ‖`, and the pinned mathlib has no quotient C-star
instance to inherit.  Two independent statements of this in the tree agree:
the "What is *not* proved here" section of `Analysis/CStarSeminormQuotient.lean`
and the "What is deliberately *not* claimed" section of
`Analysis/TracialMatrixUltraproduct.lean`, the latter naming the exact missing
lemma (for `j ∈ J₂ω` and `ε > 0` there is `e ∈ J₂ω` with `0 ≤ e ≤ 1` and
`‖j - j e‖ < ε`) together with the spectral-projection witness that should
prove it.

## A trap found by building this file

Multiplication on the quotient is **expensive to synthesize from outside the
file that defines it**.  A restatement of traciality for the bundled
functional, whose statement is the single word `x * y`, failed here with

```text
failed to synthesize HMul (TracialMatrixQuotient X ↑ω) (TracialMatrixQuotient X ↑ω) ?m
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached
```

while `1`, the module structure and the norm all resolved instantly in the
same file.  The instance is reached only by unfolding the `abbrev` to
`ModelBoundedSequence X ⧸ hilbertSchmidtNullIdeal X ↑ω` and then walking the
hand-built `SeminormedRing`/`NormedRing` instances.  It is not a missing
instance and not a `variable` ordering mistake: it is search cost.  So
traciality is *not* restated here — use `ultratrace_mul_comm` together with
`ultratraceCLM_apply`.  Anyone writing the factorization glue will meet this
at `map_mul`, and the durable fix belongs in the defining file: a directly
declared `Ring` (or `Mul`) instance for the quotient, so the search terminates
in one step instead of unfolding the ideal quotient every time.

Note the contrast with `Analysis/NormMatrixCorona.lean`, which *does* carry a
`CStarRing` instance on its quotient: there the quotient norm is the concrete
`limsup ‖a n‖` and the identity is a coordinatewise computation.  The
`‖·‖₂`-null ideal admits no such formula, which is precisely why that proof
does not transfer.
-/

namespace GroupApproximation
namespace TracialUltraproduct

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)

/-- Universe tripwire: the tracial quotient lives in `Type 0`, which is what
makes it an admissible target for the universe-relative lift out of the
maximal group C-star algebra of a group in `Type 0`. -/
example : Type := TracialMatrixQuotient X (ω : Filter ℕ)

/-- **The ultratrace as a continuous linear functional.**  Bundling only: the
bound `‖tr_ω x‖ ≤ ‖x‖` is `norm_ultratrace_le`. -/
def ultratraceCLM : TracialMatrixQuotient X (ω : Filter ℕ) →L[ℂ] ℂ :=
  (ultratraceLinearMap X ω).mkContinuous 1 fun x ↦ by
    simpa using norm_ultratrace_le X ω x

@[simp] theorem ultratraceCLM_apply
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratraceCLM X ω x = ultratrace X ω x :=
  rfl

/-- Normalization, restated for the bundled functional.  This is the
hypothesis `canonicalMaximalTrace_factorsThrough` calls `hone`, and it is
discharged here once and for all: the identity value never has to be produced
as a limit of traces of approximating matrices. -/
theorem ultratraceCLM_one :
    ultratraceCLM X ω (1 : TracialMatrixQuotient X (ω : Filter ℕ)) = 1 :=
  ultratrace_one X ω

end

end TracialUltraproduct
end GroupApproximation
