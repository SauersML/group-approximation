import GroupApproximation.GGT.HullSCLemma44KernelCone
import GroupApproximation.GGT.HullSCLemma49PowerDiagram

/-!
# Degenerate Hull 4.9 transfer models

The prefix-kernel transfer is an active Hull 4.4 frontier.  This file records
the one-point and empty-family instances that are already discharged by the
trivial-group embeddedness argument, together with the corresponding
vacuous power-diagram conclusion.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe w

/-- The kernel-cone transfer holds for every relative generating set on the
one-point source group. -/
theorem hullLemma49PrefixKernelConeTransferAt_trivialSource
    {Lambda : Type w} (D : GGT.RelGenSet PUnit.{1} Lambda) :
    PrefixKernelConeTransferAt.{0, 0, w} D :=
  prefixKernelConeTransferAt_trivialModel D

/-- The empty-relator-family instance of the preceding one-point transfer,
with all pointwise data left explicit for the vk/est handoff. -/
theorem hullLemma49PrefixKernelConeTransferAt_emptyFamily_trivialSource
    {Lambda : Type w} (D : GGT.RelGenSet PUnit.{1} Lambda)
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D
      (∅ : Set (List (GGT.RelLetter PUnit.{1} Lambda))) eps mu rho)
    {Q : Type} [Group Q] (q : PUnit.{1} →* Q)
    (hq : Function.Surjective q)
    (harea : RelativeLinearKernelArea D
      (∅ : Set (List (GGT.RelLetter PUnit.{1} Lambda))) q) :
    GGT.RelGenSet.IsHyperbolicallyEmbedded
      ((D.adjoinRelatorPrefixes (∅ : Set (List (GGT.RelLetter PUnit.{1} Lambda)))
        hsc.toIsSmallCancellation).adjoinKernel q) := by
  exact hullLemma49PrefixKernelConeTransferAt_trivialSource D
    (∅ : Set (List (GGT.RelLetter PUnit.{1} Lambda))) eps rho mu hsc q hq harea

/-- In the one-point source model, every geodesic power diagram has the
required correction, independently of the small-cancellation inputs. -/
theorem hullLemma49GeodesicPowerDiagram_trivialSource
    {Lambda : Type w} (D : GGT.RelGenSet PUnit.{1} Lambda) :
    ∀ {v : List (GGT.RelLetter PUnit.{1} Lambda)} {g : PUnit.{1}} {n : ℕ},
      IsShortestModuloConjugacy D.alphabet.carrier
        (Subgroup.normalClosure
          ({GGT.RelLetter.listVal v} : Set PUnit.{1})) g →
      Lemma49GeodesicPowerDiagram D v g n →
        ∃ k ∈ Subgroup.normalClosure
            ({GGT.RelLetter.listVal v} : Set PUnit.{1}),
          (g * k) ^ n = 1 := by
  intro v g n _hshort Z
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
