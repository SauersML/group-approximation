import GroupApproximation.Manuscript.NonMFSentences.ChainCoreClosures
import GroupApproximation.Manuscript.NonMFSentences.CoreModelsLEFClosed
import GroupApproximation.Manuscript.ChainCore.BilateralThreeCellDischarge
import GroupApproximation.Manuscript.ChainCore.BilateralThreeCoreModels
import GroupApproximation.Manuscript.ChainCore.TransientIdealDefectSpanConsumers
import GroupApproximation.Dynamics.BilateralThreeCellClopen
import GroupApproximation.Dynamics.ClopenCrossedProductCountable
import GroupApproximation.Meta.AxiomGuard

/-!
# Audit repairs for the proof of `prop:bilateral-three` (tex 1589–1603)

`non_mf_groups_exist.tex`, Section `sec:chain-core`, proof of Proposition `prop:bilateral-three`.

## The defect root (tex 1589–1594)

> The identities
> \[ [z,e_{31}(f_{-2,0})]=e_{31}(f_{-1,0}),\qquad [e_{23}(f_{0,-1}),e_{31}(f_{-1,0})]=e_{21}(d) \]
> then kill the defect root.

The corpus had the ring identities for an abstract cell (`BilateralThreeCell.Cell.commutator_z_root`,
`Cell.commutator_roots_defect`) and the kill over the cell piece.  The endpoint
`manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot` states, for a compressed clopen `P` of
the dynamical system and the printed objects `u`, `d = 1_{P∖T(P)}`, `f_{ab} = u^a d u^{-b}`,
`z = 1 + E_{33} f_{-1,-2}` (the cell `ClopenCrossedProduct.bilateralCell T k hP hTP`), both identities
with `d = ClopenCrossedProduct.defectD T k hP`, and that every homomorphism from `GL_3(R_X)` to an MF
group (in any universe) kills `e_{21}(d)`.
Route: the cell identities, `bilateralCell_d`, and the closed `rootThree_killed_of_cell
bilateralThreeCellStatement` with countability from `ClopenCrossedProduct.countable`; MF targets in
an arbitrary universe are reduced to their corona `NormMatrixCoronaUnitary Z : Type` through the
faithful representation.

## The last assertion and the LEF case (tex 1598–1603)

> The defects generate $I$ by Lemma~\ref{lem:transient-matrices}, proving the last assertion.

`manuscriptSentence_defectsGenerateTransientIdealKill`: the two-sided ideal spanned by the compressed
clopen defects is the transient ideal `I = ker (R_X → R_Y)`, and for `n ≥ 3` every homomorphism from
`GL_n(R_X)` to an MF group kills `EL_n(R_X, I)`.  Route: `defectIdeal_eq_transientIdeal_chainRecurrentSet`
and the kill clause of `printedBilateralThree_closed`.

> Otherwise Theorem~\ref{thm:core-ring-reflection} makes $R_X$, and hence its general linear groups, LEF.

`manuscriptSentence_directlyFiniteMakesLEF`: if `R_X` is directly finite then `R_X` is an LEF ring and
every `GL_n(R_X)` is LEF.  Route: `isLEFRing_of_isDedekindFiniteMonoid_of_coreModels` over the closed
`ChainCore.coreModelsLEFStatement`, then `isLEF_units_matrix_of_isLEFRing`.

Standing hypotheses of `sec:chain-core` (tex 1345): `X` nonempty compact metrizable zero-dimensional
(spelled with a chosen metric), `T` a homeomorphism, `k` a finite field.
-/

universe u

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditChain2

open scoped commutatorElement

/-- **"The identities $[z,e_{31}(f_{-2,0})]=e_{31}(f_{-1,0})$,
$[e_{23}(f_{0,-1}),e_{31}(f_{-1,0})]=e_{21}(d)$ then kill the defect root"** (tex 1589–1594). -/
theorem manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] (P : Set X) (hP : IsClopen P)
    (hTP : T '' P ⊆ P) :
    ⁅(GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).z,
        GroupApproximation.elementaryUnit (2 : Fin 3) 0 (by decide)
          ((GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).f (-2) 0)⁆ =
      GroupApproximation.elementaryUnit (2 : Fin 3) 0 (by decide)
        ((GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).f (-1) 0) ∧
    ⁅GroupApproximation.elementaryUnit (1 : Fin 3) 2 (by decide)
          ((GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).f 0 (-1)),
        GroupApproximation.elementaryUnit (2 : Fin 3) 0 (by decide)
          ((GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).f (-1) 0)⁆ =
      GroupApproximation.elementaryUnit (1 : Fin 3) 0 (by decide)
        (GroupApproximation.ClopenCrossedProduct.defectD T k hP) ∧
    ∀ (M : Type u) [Group M], GroupApproximation.IsOperatorMF M →
      ∀ f : (Matrix (Fin 3) (Fin 3) (GroupApproximation.ClopenCrossedProduct T k))ˣ →* M,
        f (GroupApproximation.elementaryUnit (1 : Fin 3) 0 (by decide)
          (GroupApproximation.ClopenCrossedProduct.defectD T k hP)) = 1 := by
  refine ⟨(GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).commutator_z_root,
    ?_, ?_⟩
  · rw [← GroupApproximation.ClopenCrossedProduct.bilateralCell_d T k hP hTP]
    exact (GroupApproximation.ClopenCrossedProduct.bilateralCell T k hP hTP).commutator_roots_defect
  · intro M _ hM f
    obtain ⟨Z, hZ, ρ, hρ⟩ := hM
    haveI : Countable (GroupApproximation.ClopenCrossedProduct T k) :=
      GroupApproximation.ClopenCrossedProduct.countable T k
    have hkill : (ρ.comp f) (GroupApproximation.elementaryUnit (1 : Fin 3) 0
        GroupApproximation.Manuscript.ChainCore.BilateralThree.idxOneNeZero
        (GroupApproximation.ClopenCrossedProduct.defectD T k hP)) = 1 :=
      GroupApproximation.Manuscript.ChainCore.BilateralThree.rootThree_killed_of_cell
        GroupApproximation.Manuscript.ChainCore.BilateralThree.bilateralThreeCellStatement T k
        (GroupApproximation.ClopenCrossedProduct.defectD T k hP) ⟨P, hP, hTP, rfl⟩
        (GroupApproximation.NormMatrixCoronaUnitary Z)
        ⟨Z, hZ, MonoidHom.id _, Function.injective_id⟩ (ρ.comp f)
    exact hρ (by rw [map_one]; exact hkill)

/-- **"The defects generate $I$ by Lemma~\ref{lem:transient-matrices}, proving the last
assertion"** (tex 1598–1599): the ideal spanned by the compressed clopen defects is
`I = ker (R_X → R_Y)`, and for `n ≥ 3` every homomorphism from `GL_n(R_X)` to an MF group kills
`EL_n(R_X, I)`. -/
theorem manuscriptSentence_defectsGenerateTransientIdealKill
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k] :
    TwoSidedIdeal.span (GroupApproximation.Manuscript.ChainCore.BilateralThree.clopenDefectSet T k) =
        GroupApproximation.ClopenCrossedProduct.transientIdeal T k
          (GroupApproximation.Dynamics.image_chainRecurrentSet T) ∧
      ∀ n : ℕ, 3 ≤ n →
        ∀ (M : Type u) [Group M], GroupApproximation.IsOperatorMF M →
          ∀ f : (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ →* M,
            ∀ g ∈ GroupApproximation.relativeElementary (Fin n)
                (GroupApproximation.ClopenCrossedProduct.transientIdeal T k
                  (GroupApproximation.Dynamics.image_chainRecurrentSet T)),
              f (g : (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ) = 1 := by
  have hspan := GroupApproximation.defectIdeal_eq_transientIdeal_chainRecurrentSet T k
  refine ⟨hspan, ?_⟩
  intro n hn M _ hM f g hg
  obtain ⟨Z, hZ, ρ, hρ⟩ := hM
  have hg' : g ∈ GroupApproximation.relativeElementary (Fin n)
      (GroupApproximation.Manuscript.ChainCore.BilateralThree.defectIdeal T k) := by
    rwa [hspan]
  have hkill : (ρ.comp f) (g : (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ) = 1 :=
    (GroupApproximation.ChainCore.ChainCoreClosures.printedBilateralThree_closed X T k n hn).2.2
      (GroupApproximation.NormMatrixCoronaUnitary Z)
      ⟨Z, hZ, MonoidHom.id _, Function.injective_id⟩ (ρ.comp f) g hg'
  exact hρ (by rw [map_one]; exact hkill)

/-- **"Otherwise Theorem~\ref{thm:core-ring-reflection} makes $R_X$, and hence its general linear
groups, LEF"** (tex 1601–1603): a directly finite `R_X` is an LEF ring, and every `GL_n(R_X)` is
LEF. -/
theorem manuscriptSentence_directlyFiniteMakesLEF
    (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (k : Type) [Field k] [Finite k]
    (hdf : IsDedekindFiniteMonoid (GroupApproximation.ClopenCrossedProduct T k)) :
    GroupApproximation.Pestov91.IsLEFRing (GroupApproximation.ClopenCrossedProduct T k) ∧
      ∀ n : ℕ, GroupApproximation.IsLEF
        (Matrix (Fin n) (Fin n) (GroupApproximation.ClopenCrossedProduct T k))ˣ := by
  have hR : GroupApproximation.Pestov91.IsLEFRing (GroupApproximation.ClopenCrossedProduct T k) :=
    GroupApproximation.Manuscript.ChainCore.BilateralThree.isLEFRing_of_isDedekindFiniteMonoid_of_coreModels
      GroupApproximation.ChainCore.coreModelsLEFStatement T k hdf
  exact ⟨hR, fun n ↦
    GroupApproximation.Manuscript.ChainCore.BilateralThree.isLEF_units_matrix_of_isLEFRing hR n⟩

end AuditChain2
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditChain2.manuscriptSentence_bilateralThreeIdentitiesKillDefectRoot
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditChain2.manuscriptSentence_defectsGenerateTransientIdealKill
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditChain2.manuscriptSentence_directlyFiniteMakesLEF
