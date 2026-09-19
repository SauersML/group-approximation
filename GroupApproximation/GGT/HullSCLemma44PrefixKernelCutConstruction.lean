import GroupApproximation.GGT.HullSCLemma44KernelGeodesicInductionConstruction
import GroupApproximation.GGT.HullSCLemma44PrefixKernelTransferInduction

/-!
# The prefix-cone cut induction assembly

Osin's prefix-cone induction uses the kernel-geodesic cut output together with
a one-step cone-ball cut.  `PrefixKernelConeCutData` makes the latter output
explicit: a source-radius function and, at each cone-ball radius, either a
source peripheral lift or a predecessor cone-ball element.  The theorem below
reuses `kernelGeodesicCutInductionAt_of_data` for the first component and the
explicit cone payload for the second component, then applies the already proved
finite-ball induction.

The two outputs are independent at a fixed quotient, while the first one is
the least-area certificate cut from `HullSCLemma44KernelGeodesicCut`.  The
one-point model uses kernel constant zero and source radius zero by equality.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u v w

/-- Explicit one-step output for a prefix-cone peripheral ball. -/
structure PrefixKernelConeCutData
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) where
  radius : ℕ → ℕ
  cut : ∀ (lam : Lambda) (n : ℕ) (y : G),
    y ∈ ((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n →
      y ∈ D.relBall lam (radius n) ∨
        (0 < n ∧ y ∈ ((D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).adjoinKernel q).relBall lam (n - 1))

/-- The explicit cone payload has the exact one-step form consumed by the
finite relative-ball induction. -/
theorem PrefixKernelConeCutData.toOneStep
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    {hsc : RelWord.IsLemma44Input D W eps mu rho}
    {q : G →* Q}
    (data : PrefixKernelConeCutData D W eps rho mu hsc q) :
    PrefixKernelConeOneStepCutAt D W eps rho mu hsc q :=
  ⟨data.radius, data.cut⟩

/-- The two explicit cut payloads produce the complete prefix-cone induction
premise.  The first conjunct is obtained by an actual strong induction on the
kernel-geodesic measure; the second is the supplied cone one-step output. -/
theorem prefixKernelConeCutInductionAt_of_data
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hkernelData : ∃ M : ℕ, ∀ (area : ℕ) (endpoint : G),
      endpoint ∈ q.ker → ∀ word : List G,
        (∀ x ∈ word,
          x ∈ (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier) →
        word.prod = endpoint →
        word.length = wordDist
          (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier 1 endpoint →
        word.length = area → word.prod ≠ 1 →
        Nonempty (KernelGeodesicCutData D W eps rho mu hsc q M area word))
    (hconeData : PrefixKernelConeCutData D W eps rho mu hsc q) :
    KernelGeodesicCutInductionAt D W eps rho mu hsc q ∧
      PrefixKernelConeOneStepCutAt D W eps rho mu hsc q := by
  have hkernel : KernelGeodesicCutInductionAt D W eps rho mu hsc q :=
    kernelGeodesicCutInductionAt_of_data D W eps rho mu hsc hmu hrho q hq
      hker hkernelData
  exact ⟨hkernel, hconeData.toOneStep⟩

/-- At a fixed quotient, the concrete kernel and cone payloads give cone
hyperbolic embeddedness.  The kernel-geodesic estimate is the first output of
the same area induction used in `prefixKernelConeCutInductionAt_of_data`. -/
theorem prefixKernelConeEmbedded_of_data
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (hkernelData : ∃ M : ℕ, ∀ (area : ℕ) (endpoint : G),
      endpoint ∈ q.ker → ∀ word : List G,
        (∀ x ∈ word,
          x ∈ (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier) →
        word.prod = endpoint →
        word.length = wordDist
          (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier 1 endpoint →
        word.length = area → word.prod ≠ 1 →
        Nonempty (KernelGeodesicCutData D W eps rho mu hsc q M area word))
    (hconeData : PrefixKernelConeCutData D W eps rho mu hsc q) :
    ((D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation).adjoinKernel q).IsHyperbolicallyEmbedded := by
  have hcuts := kernelGeodesicCutInductionAt_of_data D W eps rho mu hsc hmu hrho
    q hq hker hkernelData
  have hkernel := kernelGeodesicEstimateAt_of_cutInduction D W eps rho mu
    hsc q hcuts
  exact isHyperbolicallyEmbedded_prefixKernelCone_of_kernelEstimate_and_oneStepCuts
    D hD W hsc q hkernel hconeData.toOneStep

/-! ## Degenerate model -/

/-- In the one-point source the cone cut has source radius zero exactly. -/
theorem prefixKernelConeCutData_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : PUnit →* Q) :
    ∃ data : PrefixKernelConeCutData D W eps rho mu hsc q,
      data.radius 0 = 0 := by
  refine ⟨{ radius := fun _ => 0, cut := ?_ }, rfl⟩
  intro lam n y hy
  left
  rw [GGT.RelGenSet.relBall_zero]
  exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

end HullSC
end GroupApproximation
