import GroupApproximation.Kazhdan.HaagerupAffineSums
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.Analysis.Complex.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The two interfaces of Guentner--Higson--Weinberger's Theorem 4

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex line 1146):

> Every countable subgroup of `GL_2` over a field has the Haagerup property [GHW, Theorem 4] …

Guentner--Higson--Weinberger (*The Novikov conjecture for linear groups*, Publ. Math. IHÉS 101
(2005), §5) build a proper negative-type function from one negative-type function per valuation
of a finitely generated field: tree distances at discrete valuations, hyperbolic distances at
archimedean ones.  This module fixes the two archimedean statements that the assembly
`Kazhdan/GHWPlaces` consumes.

* `GHWArchimedeanAffineBound`: an affine isometric action of any group mapping to `GL_2(ℂ)`
  whose translation part dominates the matrix entries,
  `|g_ij|² ≤ 2 |det g| exp ‖b γ‖²`.  This is GHW's Lemmas 8 and 10 together, with
  `‖b γ‖²` standing for the hyperbolic displacement `d(x₀, g x₀)` and
  `cosh d(x₀, g x₀) = ‖g‖²_F / (2 |det g|)`.
* `GHWComplexEmbeddingExtension`: a characteristic-zero field algebraic over `ℚ(t)` embeds into
  `ℂ` with prescribed algebraically independent values on `t` (the archimedean extensions of
  GHW's §2, Lemma 2).

## Manuscript status

Interface definitions for the Toeplitz--Jacobson remark; certify no printed sentence on their own.
-/

namespace GroupApproximation
namespace GHW

/-- **The archimedean affine bound** (GHW, Lemmas 8 and 10). -/
def GHWArchimedeanAffineBound : Prop :=
  ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) ℂ),
    ∃ A : GroupApproximation.Haagerup.AffineAction.{0, 0} Γ, ∀ (γ : Γ) (i j : Fin 2),
      ‖((ρ γ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ≤
        2 * ‖((ρ γ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ * Real.exp (‖A.b γ‖ ^ 2)

/-- **The complex embedding extension of GHW's archimedean places.** -/
def GHWComplexEmbeddingExtension : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [Countable K] {ι : Type} [Finite ι]
    (t : ι → K), AlgebraicIndependent ℚ t → Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) K →
    ∀ z : ι → ℂ, AlgebraicIndependent ℚ z → ∃ σ : K →+* ℂ, ∀ i, σ (t i) = z i

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.GHWArchimedeanAffineBound
#audit_axioms GroupApproximation.GHW.GHWComplexEmbeddingExtension
