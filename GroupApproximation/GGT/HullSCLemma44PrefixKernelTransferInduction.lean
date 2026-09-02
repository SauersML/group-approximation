import GroupApproximation.GGT.HullSCLemma44KernelGeodesicInduction
import GroupApproximation.GGT.HullSCLemma44PrefixKernelBallInduction
import GroupApproximation.GGT.HullSCLemma44KernelCone
import GroupApproximation.GGT.HullSCLemma44RelativeArea

/-!
# Prefix-kernel transfer from the two cut inductions

Osin's relative Dehn proof has two independent outputs.  A least-area cut of
an old geodesic gives a uniform kernel-cone prefix bound, while a cut of a
cone peripheral ball gives either a bounded source peripheral element or a
strictly smaller cone ball.  `PrefixKernelConeCutInductionAt` names exactly
these two outputs at fixed parameters.  The theorem below combines them with
the hyperbolic-enlargement criterion and the finite-ball induction, so the
remaining geometric work is isolated in one strictly smaller premise.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-- The two local inductions required for a prefix-kernel cone.  The first
component is the uniform bound on prefixes of an old-alphabet geodesic ending
in the kernel.  The second is the one-step peripheral-ball cut, with a source
radius function and a predecessor cone ball. -/
def PrefixKernelConeCutInductionAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q)
    (_hq : Function.Surjective q),
    RelativeLinearKernelArea D W q →
      KernelGeodesicEstimateAt D W eps rho mu hsc q ∧
        PrefixKernelConeOneStepCutAt D W eps rho mu hsc q

/-- Uniform form of the two-cut premise over hyperbolically embedded source
families. -/
def PrefixKernelConeCutInductionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      PrefixKernelConeCutInductionAt.{u, v, w} D

/-- The two cut inductions produce the pointwise prefix-kernel transfer. -/
theorem prefixKernelConeTransferAt_of_cutInduction
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (hcut : PrefixKernelConeCutInductionAt.{u, v, w} D) :
    PrefixKernelConeTransferAt.{u, v, w} D := by
  intro W eps rho mu hsc Q _ q hq harea
  obtain ⟨hkernel, hball⟩ := hcut W eps rho mu hsc q hq harea
  exact isHyperbolicallyEmbedded_prefixKernelCone_of_kernelEstimate_and_oneStepCuts
    D hD W hsc q hkernel hball

/-- The two cut inductions produce Osin's uniform prefix-kernel transfer. -/
theorem prefixKernelConeTransferStatement_of_cutInduction
    (hcut : PrefixKernelConeCutInductionStatement.{u, v, w}) :
    PrefixKernelConeTransferStatement.{u, v, w} := by
  intro G _ Lambda D hD
  exact prefixKernelConeTransferAt_of_cutInduction D hD (hcut D hD)

/-! ## One-point model -/

/-- On a one-point source, the geodesic branch has bound `M = 0` and the
peripheral-ball branch has source radius zero. -/
theorem prefixKernelConeCutInductionAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    PrefixKernelConeCutInductionAt.{0, v, w} D := by
  intro W eps rho mu hsc Q _ q hq _harea
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hbound⟩ :=
      kernelGeodesicEstimateAt_trivialModel_zero D W eps rho mu hsc q hq
    exact ⟨M, hbound⟩
  · exact prefixKernelConeOneStepCutAt_trivialModel D W eps rho mu hsc q

end HullSC
end GroupApproximation
