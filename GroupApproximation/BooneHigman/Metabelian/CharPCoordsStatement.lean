import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Polynomial coordinates in characteristic `p`: statements (lane bh-met-03)

Research node `char-p-linear-groups-embed-in-polynomial-f-p-groups`: "every finitely generated
subgroup of `GL_n(K)`, `K` a field of characteristic `p > 0`, embeds in
`GL_M(F_p[x_1, ..., x_k])` for some `M, k`".  Route of
`char-p-polynomial-embedding-via-noether-normalization`: the matrix entries of a finite
generating set lie in a finitely generated `F_p`-subalgebra `A ⊆ K`; Noether normalization makes
`A` a finite module over `P = F_p[x_1, ..., x_s]`; generic freeness makes `A[1/f]` free over
`P[1/f]`; so `A ⊆ A[1/f]` embeds in matrices over `P[1/f]`, and `P[1/f]` embeds in matrices
over `P`.

* `CharPPolynomialCoordinatesStatement` is the lane target.
* `FiniteDomainAwayEmbeddingStatement` is the one isolated remaining input (generic freeness).

**Why the isolated statement is true.**  Let `φ : P = k[x_0, ..., x_{s-1}] → R` be injective
and finite, `R` a domain, `L = Frac P`.  Pick `r_1, ..., r_m ∈ R` forming an `L`-basis of
`L ⊗_P R` and generators `y_1, ..., y_N` of `R` as a `P`-module; write
`y_j = Σ_i c_{ji} r_i` with `c_{ji} ∈ L`, and let `f ≠ 0` be a common denominator.  Then the
`r_i` are a `P[1/f]`-basis of `R[1/f]` (they span, and they are independent over `L`), so
`R[1/f]` embeds in `M_m(P[1/f])` by left multiplication; and `R → R[1/f]` is injective because
`R` is a domain and `φ f ≠ 0`.  (This is generic freeness, Mathlib's
`Module.FinitePresentation.exists_free_localizedModule_powers`, plus left multiplication.)

**Why it is strictly smaller than the target.**  The reduction
`charPPolynomialCoordinatesStatement_of_finiteDomainAwayEmbedding`
(in `CharPCoordsAssembly.lean`) supplies everything else and is proved: the characteristic
`p` bookkeeping, the finitely generated subring (`Coordinates.exists_finset_factor`), Noether
normalization (`exists_finite_inj_algHom_of_fg`), the removal of the denominator
`P[1/f] ↪ M(P)` (`CharPCoords.matrixEmbedding_localizationAway`, via Nagata's change of variables
and a monic `AdjoinRoot`), and the passage from rings to `GL`.  The isolated statement mentions
no group, no field `K`, no characteristic, and no Noether normalization: it is a single
commutative-algebra lemma about one finite injective extension of a polynomial ring.
-/

open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords

/-- **Lane target.**  Every finitely generated subgroup of `GL_n(K)`, with `K` a field of
characteristic `p > 0`, embeds in `GL_M(F_p[x_0, ..., x_{k-1}])` for some `k, M`. -/
def CharPPolynomialCoordinatesStatement : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 0 < p → ringChar K = p →
    ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      ∃ k M : ℕ, ∃ ψ : H →* Matrix.GeneralLinearGroup (Fin M) (MvPolynomial (Fin k) (ZMod p)),
        Function.Injective ψ

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.CharPPolynomialCoordinatesStatement

/-- **Isolated input (generic freeness).**  A domain `R` that is a finite injective extension
of a polynomial ring `P = k[x_0, ..., x_{s-1}]` over a field embeds in a matrix ring over
`P[1/f]` for some `f ∈ P`. -/
def FiniteDomainAwayEmbeddingStatement : Prop :=
  ∀ (k : Type) [Field k] (s : ℕ) (R : Type) [CommRing R] [IsDomain R]
    (φ : MvPolynomial (Fin s) k →+* R), Function.Injective φ → φ.Finite →
      ∃ f : MvPolynomial (Fin s) k, MatrixEmbedding R (Localization.Away f)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.FiniteDomainAwayEmbeddingStatement

end GroupApproximation.BooneHigman.Metabelian.CharPCoords
