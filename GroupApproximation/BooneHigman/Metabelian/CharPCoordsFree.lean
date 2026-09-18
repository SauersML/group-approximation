import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFreeMul
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Generic freeness for a finite injective extension of a polynomial ring (lane bh-met-10)

Research node `char-p-polynomial-embedding-via-noether-normalization`: "generic freeness makes
`A[1/f]` free over `P[1/f]`; so `A ⊆ A[1/f]` embeds in matrices over `P[1/f]`".

**Endpoint.** `finiteDomainAwayEmbedding : FiniteDomainAwayEmbeddingStatement`.

**Route.**
1. `P` is a Noetherian domain and `A` is a finite `P`-module, so `A` is finitely presented
   (`Module.finitePresentation_of_finite`).
2. Over the fraction field `L = Frac P`, the localized module `L ⊗ A = LocalizedModule P⁰ A`
   is a finite-dimensional vector space; choose a basis (`Module.Free.chooseBasis`).
3. Mathlib's `Module.FinitePresentation.exists_basis_localizedModule_powers` lifts that basis
   to a `P[1/r]`-basis of `A[1/r]` for some nonzero divisor `r ∈ P⁰`, so `r ≠ 0`.
4. `matrixEmbedding_of_basis_away` (left multiplication on `A[1/r]`, faithful because `A` is
   a domain and `P → A` is injective) gives `A ↪ M_N(P[1/r])`.
-/

open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords

/-- **Generic freeness, algebra form.**  A domain `A` that is a finite algebra over a Noetherian
domain `P`, with `P → A` injective, embeds in a matrix ring over `P[1/r]` for some `r ∈ P`. -/
theorem exists_matrixEmbedding_away {P A : Type*} [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [CommRing A] [IsDomain A] [Algebra P A] [Module.Finite P A]
    (hinj : Function.Injective (algebraMap P A)) :
    ∃ r : P, MatrixEmbedding A (Localization.Away r) := by
  haveI : Module.FinitePresentation P A := Module.finitePresentation_of_finite P A
  obtain ⟨r, hr, b, -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    (nonZeroDivisors P) (LocalizedModule.mkLinearMap (nonZeroDivisors P) A) (FractionRing P)
    (Module.Free.chooseBasis (FractionRing P) (LocalizedModule (nonZeroDivisors P) A))
  exact ⟨r, matrixEmbedding_of_basis_away hinj (nonZeroDivisors.ne_zero hr) b⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.exists_matrixEmbedding_away

/-- **The isolated input of lane bh-met-03, proved.**  A domain `R` that is a finite injective
extension of `P = k[x_0, ..., x_{s-1}]` embeds in a matrix ring over `P[1/f]` for some `f`. -/
theorem finiteDomainAwayEmbedding : FiniteDomainAwayEmbeddingStatement := by
  intro k _ s R _ _ φ hinj hfin
  letI : Algebra (MvPolynomial (Fin s) k) R := φ.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) R := hfin
  exact exists_matrixEmbedding_away (P := MvPolynomial (Fin s) k) (A := R) hinj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.finiteDomainAwayEmbedding

end GroupApproximation.BooneHigman.Metabelian.CharPCoords
