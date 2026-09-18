import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2 without the block bookkeeping: the Statement

Lane `bh-met-91b`.  Target: `SuslinR2IndBaseStatement` (`SuslinR2IndFamily.lean`), i.e.
`SuslinR2BlockLocal A 3` for the two families.

**The residual.**  `SuslinBase3StabLocal A n`: for every `σ ∈ SL_n(A[X])` with `σ(0) = 1` and
every maximal ideal `𝔪`, the stabilization `diag(σ_𝔪, 1)` lies in `E_{n+1}(A_𝔪[X])`.  It is
used only at `n = 2`: a GLOBAL `2 × 2` matrix, with no auxiliary elementary factor `F`, no
coordinate block, no reindexing and no localized denominators.

This file holds the definition and two functoriality lemmas: a ring map commutes with
stabilization and with reindexing.  The reductions are in `SuslinBase3Reduce.lean`.  The family
endpoint and the root companion are in `SuslinBase3Endpoint.lean`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The stabilized normalized residual** at rank `n`.  For every `σ ∈ SL_n(A[X])` with
`σ(0) = 1` and every maximal `𝔪`, `diag(σ_𝔪, 1) ∈ E_{n+1}(A_𝔪[X])`.  It is used at `n = 2`.
It is TRUE for the two families, by Suslin's theorem, as a truth check only
(`suslinBase3_global_of_localCaseFamily`).  It is NOT asserted for general `A`: its content is
a `K₁`-regularity statement, and `K₁`-regularity fails for non-regular rings such as the cusp
`k[t², t³]` (`NK₁ ≠ 0`). -/
def SuslinBase3StabLocal (A : Type*) [CommRing A] (n : ℕ) : Prop :=
  ∀ σ : Matrix.GeneralLinearGroup (Fin n) (Polynomial A),
    Matrix.det (σ : Matrix (Fin n) (Fin n) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) σ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
              (elementaryMatrixUnitMap (ι := Fin n)
                (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ) ∈
            elementaryGroup (Fin n ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3StabLocal

/-- A ring map commutes with block stabilization `u ↦ diag(u, 1)`. -/
theorem suslinBase3_map_stabilize {R S ι κ : Type*} [CommRing R] [CommRing S] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : R →+* S) (u : (Matrix ι ι R)ˣ) :
    elementaryMatrixUnitMap f (stabilizeUnit (R := R) (κ := κ) u) =
      stabilizeUnit (R := S) (κ := κ) (elementaryMatrixUnitMap f u) := by
  apply Units.ext
  ext i j
  change f (Matrix.fromBlocks (u : Matrix ι ι R) 0 0 1 i j) =
    Matrix.fromBlocks (f.mapMatrix (u : Matrix ι ι R)) 0 0 1 i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₂]
    exact (suslinR2Ind_one_apply_map f i j).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_map_stabilize

/-- A ring map commutes with reindexing along `e : ι ≃ κ`. -/
theorem suslinBase3_map_reindex {R S ι κ : Type*} [CommRing R] [CommRing S] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : R →+* S) (e : ι ≃ κ)
    (u : (Matrix ι ι R)ˣ) :
    elementaryMatrixUnitMap f (elementaryReindexUnitEquiv (R := R) e u) =
      elementaryReindexUnitEquiv (R := S) e (elementaryMatrixUnitMap f u) := by
  apply Units.ext
  ext i j
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3_map_reindex

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
