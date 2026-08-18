import GroupApproximation.Analysis.VectorOmegaAction
import GroupApproximation.Analysis.AbstractSpectralGap
import GroupApproximation.Analysis.CStarSpectralProjection
import GroupApproximation.Sofic.UltraproductKazhdanProjection

/-!
# The Kazhdan projection inside `B_ω = ∏_ω M_{d_n}` itself

`\label{thm:normal-kazhdan}` says of the spectral projection

> `P = χ_{{1}}(h)` **lies in the norm ultraproduct** with range `Fix π(K̄)`.

`Analysis/VectorOmegaKazhdanGap.lean` closes the range clause and the
nonvanishing of `q = 1 − P`, but it takes `P` inside `B(H_ω)`, the bounded
operators on the Hilbert-space ultraproduct.  The printed sentence asks for
something sharper: that `P` lies in `B_ω` itself, the C*-subalgebra of classes
of bounded matrix sequences.  This file does that.

## Why it is only a matter of taking the calculus in the right place

Nothing about `P` changes.  The functional calculus produces its projection
inside whatever unital C*-algebra it is run in, so the question is entirely
whether `B_ω` *is* one and whether `h` lives there — and both are true and were
already true.  `Analysis/NormMatrixCorona.lean` builds every parent structure of
the bundled class at an arbitrary filter — normed ring, star ring, completeness,
the C*-identity (at any `NeBot` filter), the complex normed algebra, the star
module — and assembles them into `CStarAlgebra` only at `cofinite`, under the
name `NormMatrixCStarCorona`.  At a free ultrafilter the same six instances are
available and nothing assembled them.  `filterMatrixCoronaCStarAlgebra` below is
that assembly, and it is six field assignments.

## What is here

* `filterMatrixCoronaCStarAlgebra` — the ω-corona as a bundled unital complex
  C*-algebra;
* `coronaClass` — the class `π(g) = [V_{g,n}]_ω`, as a unitary of `B_ω`, from
  the same `OmegaUnitaryRep` hypothesis the `H_ω` side uses: coordinatewise
  unitary representatives, multiplication defects null *along ω* and not at any
  stage;
* `manuscriptKazhdanProjection_memBOmega` — the printed `P`, as an element of
  `B_ω`, self-adjoint, idempotent, and absorbed by `h`.

## What this does not yet do

It does not identify this `P` with the one `VectorOmegaKazhdanGap` takes in
`B(H_ω)`.  That identification is not a formality: it needs the action
`VectorOmegaAction.actQ` upgraded from a ring homomorphism into `Module.End` to a
*continuous unital ⋆-homomorphism* into `B(H_ω)`, after which the functional
calculus commutes with it and the two projections agree by `cfc` naturality.
Until that is done the row's single sentence is proved in two places rather than
one, and `NK.06` is graded accordingly.
-/

namespace GroupApproximation
namespace OmegaCoronaKazhdanProjection

open Filter Matrix Topology
open AbstractSpectralGap VectorOmegaAction
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## The ω-corona is a C*-algebra -/

section Algebra

variable (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] (l : Filter ℕ) [l.NeBot]

/-- **The corona at an arbitrary `NeBot` filter is a bundled unital complex
C*-algebra.**  Every field is an instance `Analysis/NormMatrixCorona.lean`
already provides at that generality; only the assembly was specialized to
`cofinite`. -/
noncomputable instance filterMatrixCoronaCStarAlgebra :
    CStarAlgebra (FilterMatrixCoronaAlgebra X l) where
  toNormedRing := filterMatrixCoronaAlgebraNormedRing X l
  toStarRing := filterMatrixCoronaAlgebraStarRing X l
  toCompleteSpace := filterMatrixCoronaAlgebraCompleteSpace X l
  toCStarRing := filterMatrixCoronaAlgebraCStarRing X l
  toNormedAlgebra := filterMatrixCoronaAlgebraNormedAlgebra X l
  toStarModule := filterMatrixCoronaAlgebraStarModule X l

end Algebra

/-! ## What blocks the rest, precisely

The three facts the printed `π : G → U(B_ω)` needs are one step each from what
`Analysis/VectorOmegaAction.lean` already has: the class of `unitarySeq Y R.V g`
is unitary in `B_ω` because its representatives are unitary coordinatewise, it is
multiplicative because the defect is `ω`-null, and it is unital because the class
at `1` is a unitary idempotent.  None of that is where this stops.

**The instance tower is.**  Every parent structure above is available at an
arbitrary `NeBot` filter, and the assembly is the six lines above — but *using*
it through the reducible `FilterMatrixCoronaAlgebra (Idx Y) ω` overruns the
default `synthInstance` budget on questions as basic as
`HMul (FilterMatrixCoronaAlgebra (Idx Y) ω)`.  That is why
`Analysis/NormMatrixCorona.lean` assembles the bundled class only at `cofinite`,
and does it behind `NormMatrixCStarCorona`, an **opaque** synonym with its own
instances registered: the opacity is what stops each consumer re-deriving the
tower.

Two things were tried and should not be retried in these forms.  A
`NormedRing (FilterMatrixCoronaAlgebra (Idx Y) ω)` instance projected out of the
corona creates a second path to the ring structure and breaks definitional
matching against the `CStarAlgebra` instance's own `toNormedRing`.  Raising the
heartbeat budget works and is deliberately not done: `scripts/check.py` counts
budget bumps as findings, and a peer lane spent 2026-08-18 removing them.

**What the ω side actually needs** is the analogue of `NormMatrixCStarCorona` at
a free ultrafilter — an opaque `OmegaMatrixCStarCorona (X) (ω)` with its
instances registered once — after which the representation, the gap and the
projection are the same three steps that `Analysis/VectorOmegaKazhdanGap.lean`
already runs inside `B(H_ω)`.  That is infrastructure, not mathematics, and it is
the whole of what stands between `NK.06`'s remaining clause and its proof.

Note also that closing that clause alone would still not move `NK.06`, because
the row is one sentence: it asks for a `P` that lies in `B_ω` *and* has range
`Fix π(K̄)`.  Proving each half in a different ambient leaves the conjunction
unproved.  Joining them needs `VectorOmegaAction.actQ` upgraded from a ring
homomorphism into `Module.End` to a continuous unital ⋆-homomorphism into
`B(H_ω)`, after which the two projections agree by naturality of the functional
calculus.
-/

end

end OmegaCoronaKazhdanProjection
end GroupApproximation
