import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.PolarLiftingGeneralCStar

/-!
# The printed lifting step at the printed blocks

`\label{lem:lift}` opens its proof with

> lift to a bounded sequence; unitarity gives `‖xₙ*xₙ − 1‖ → 0`.

`Analysis/PolarLiftingGeneralCStar.printedUnitaryLifting` proves that sentence,
and the rest of the printed paragraph, for an arbitrary sequence of unital
C*-algebras.  Ledger row `PRE.09` could not cite it for a reason that is neither
the mathematics nor the generality: the pinned mathlib has
`CStarRing (Matrix Z Z ℂ)` under the L2 operator norm but no **bundled**
`CStarAlgebra (Matrix Z Z ℂ)`, so matrix blocks were not an instance of the
general theorem.

Every parent of the bundled class is there — normed ring, star ring,
completeness, the C*-identity, the complex normed algebra, the star module — so
what was missing is an assembly, not a structure.

## Why the instance is local, and why it is stated at a single block

`Matrix` carries several norms in mathlib and they are scoped deliberately.
Registering a bundled `CStarAlgebra` for one of them globally would decide that
choice for every file that mentions a matrix, including files that want the
Frobenius or the sup norm.  A `local instance` decides it inside this file only,
and the elaborated statement below carries the instance term with it, so a
consumer citing the theorem gets the same structure without inheriting the
choice.

It is stated for a single index type rather than for a family: written as
`(n : ℕ) → CStarAlgebra (Matrix (X n) (X n) ℂ)` against a family variable it is
a parametric local instance whose `ℕ` parameter has no forward dependencies, and
Lean declines to use it.  At a single block there is no such parameter.

The index family here is a bare `ℕ → Type` with its finiteness and decidability
as instance arguments, matching `Analysis/NormMatrixCorona.lean`, rather than
`FiniteModel`: the coercion that makes a `FiniteModel` a sort lives in
`Sofic/Sofic.lean`, which neither import brings in, and the mismatch shows up as
`Nonempty (X n)` failing to elaborate rather than as a missing import.
-/

namespace GroupApproximation
namespace PolarLiftingMatrixBlocks

open Filter Topology
open PolarLiftingGeneralCStar
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The bundled C*-algebra structure on one matrix block at the L2 operator
norm.  Six field assignments, every one of them an instance already. -/
local instance matrixBlockCStarAlgebra (Z : Type) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

/-- **`PRE.09`, at the printed blocks.**

> lift to a bounded sequence; unitarity gives `‖xₙ*xₙ − 1‖ → 0`.

The printed step, for the matrix coordinates `lem:lift` is stated about, at an
arbitrary filter — the `cofinite` case being the printed one, where the
denominator is the operator-norm `c₀` ideal.  Both Gram defects, which are the
printed sentence's two halves.  The remainder of the printed paragraph —
invertibility for large `n`, unitarity of the polar correction, and its
convergence — is the rest of `printedUnitaryLifting` at the same
instantiation. -/
theorem gram_defects_tendsto_matrixBlocks (l : Filter ℕ)
    (x : BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ))
    (hq : Ideal.Quotient.mk
        (nullCStarSequenceIdeal (fun n ↦ Matrix (X n) (X n) ℂ) l) x ∈
      unitary (CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) l)) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) l (nhds 0) ∧
      Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) l (nhds 0) :=
  ⟨(printedUnitaryLifting (fun n ↦ Matrix (X n) (X n) ℂ) l x hq).1,
    (printedUnitaryLifting (fun n ↦ Matrix (X n) (X n) ℂ) l x hq).2.1⟩

end

end PolarLiftingMatrixBlocks
end GroupApproximation
