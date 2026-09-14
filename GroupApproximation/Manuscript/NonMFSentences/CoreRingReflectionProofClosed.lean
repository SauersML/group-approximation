import GroupApproximation.Manuscript.NonMFSentences.CoreRingReflection
import GroupApproximation.Manuscript.NonMFSentences.CoreModelsLEFClosed
import GroupApproximation.Algebra.DirectlyFiniteCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:core-ring-reflection`: the amplification step of the proof, closed

`non_mf_groups_exist.tex`, proof of Theorem `thm:core-ring-reflection` (tex 1531–1537):

> Now let $\phi\colon M_m(R_X)\to A$ be unital with $A$ directly finite.  The corner
> $\phi(E_{11})A\phi(E_{11})$ is directly finite.  Apply the preceding argument to the unital map
> $r\mapsto\phi(rE_{11})$ into this corner.  Multiplication by the other matrix units shows that
> $\phi$ kills $M_m(I)$.  Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite ring
> tables.

`CoreRingReflection` proves these steps for an abstract surjection, and in `R_X` over "`R_Y` is LEF".  This
module records each printed step at `R_X → R_Y` as a named Prop with nothing assumed.

* `PrintedCoreCornerMapKillsKernel`, `printedCoreCornerMapKillsKernel` (tex 1534–1535): the unital map
  `r ↦ φ(r E_ii)` into the directly finite corner kills `I = ker(R_X → R_Y)`.
* `PrintedCoreMatrixKillsKernel`, `printedCoreMatrixKillsKernel` (tex 1535–1536): every unital map from
  `M_m(R_X)` to a directly finite ring kills `M_m(I)`.
* `PrintedCoreMatrixQuotientLEF`, `printedCoreMatrixQuotientLEF` (tex 1536–1537): `M_m(R_Y)` is LEF, from
  "`R_Y` is LEF" (`coreModelsLEFStatement`) entrywise (`Pestov91.IsLEFRing.matrix`).
-/

namespace GroupApproximation.ChainCore.CoreRingReflection

open MFQuotientUnits

universe w

/-- **"Apply the preceding argument to the unital map $r\mapsto\phi(rE_{11})$ into this corner"**
(tex 1534–1535): for every unital `φ : M_m(R_X) → A` with `A` directly finite and every index `i`, the
unital map `r ↦ φ(r E_ii)` into the corner at `φ(E_ii)` kills `I = ker(R_X → R_Y)`. -/
def PrintedCoreCornerMapKillsKernel : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ) (A : Type w) [Ring A] [IsDedekindFiniteMonoid A]
    (φ : Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k) →+* A) (i : Fin m)
    (x : ClopenCrossedProduct T k),
    GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k x = 0 →
      matrixUnitCornerHom φ i x = 0

theorem printedCoreCornerMapKillsKernel : PrintedCoreCornerMapKillsKernel.{w} := by
  intro X _ _ _ T k _ m A _ _ φ i x hx
  exact killsKernelOfDirectlyFinite_coreRestrict.{w} T k _ (matrixUnitCornerHom φ i) x hx

/-- **"Multiplication by the other matrix units shows that $\phi$ kills $M_m(I)$"** (tex 1535–1536):
every unital map from `M_m(R_X)` to a directly finite ring kills the kernel of `M_m(R_X) → M_m(R_Y)`. -/
def PrintedCoreMatrixKillsKernel : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] (m : ℕ),
    KillsKernelOfDirectlyFinite.{w}
      ((GroupApproximation.ChainCore.DynamicRankBudget.coreRestrict T k).mapMatrix :
        Matrix (Fin m) (Fin m) (ClopenCrossedProduct T k) →+* _)

theorem printedCoreMatrixKillsKernel : PrintedCoreMatrixKillsKernel.{w} := by
  intro X _ _ _ T k _ m
  exact killsKernelOfDirectlyFinite_mapMatrix.{w} _ (killsKernelOfDirectlyFinite_coreRestrict.{w} T k) m

/-- **"Its quotient $M_m(R_Y)$ is LEF, as follows entrywise from finite ring tables"** (tex 1536–1537). -/
def PrintedCoreMatrixQuotientLEF : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] (m : ℕ),
    Pestov91.IsLEFRing (Matrix (Fin m) (Fin m)
      (ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T (DynamicRankBudget.image_core T)) k))

theorem printedCoreMatrixQuotientLEF : PrintedCoreMatrixQuotientLEF := by
  intro X _ _ _ _ T k _ _ m
  exact (coreModelsLEFStatement X T k).matrix (Fin m)

end GroupApproximation.ChainCore.CoreRingReflection

#audit_closed_axioms GroupApproximation.ChainCore.CoreRingReflection.printedCoreCornerMapKillsKernel
#audit_closed_axioms GroupApproximation.ChainCore.CoreRingReflection.printedCoreMatrixKillsKernel
#audit_closed_axioms GroupApproximation.ChainCore.CoreRingReflection.printedCoreMatrixQuotientLEF
