import GroupApproximation.GGT.HullSCLemma44KernelAssembly

/-!
# Relative-ball induction for the prefix kernel cone

The relative Dehn argument proves local finiteness by cutting an element of a
cone peripheral ball.  At radius `n + 1`, one cut either lifts the element to a
fixed source peripheral ball or puts it in the cone ball of radius `n`.  The
induction below turns this one-step cut output into finite cone peripheral
balls.  The final theorem combines those finite balls with the kernel-geodesic
estimate and Osin's enlargement criterion.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-- A one-step relative Dehn cut for the prefix kernel cone.  `radius` bounds
the source peripheral ball in the lift branch; the second branch decreases the
induction measure by one. -/
def PrefixKernelConeOneStepCutAt
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) : Prop :=
  ∃ radius : ℕ → ℕ, ∀ (lam : Lambda) (n : ℕ) (y : G),
    y ∈ ((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n →
      y ∈ D.relBall lam (radius n) ∨
        (0 < n ∧ y ∈ ((D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).adjoinKernel q).relBall lam (n - 1))

/-- One-step cuts imply finite relative balls in the prefix kernel cone. -/
theorem locallyFinite_prefixKernelCone_of_oneStepCuts
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q)
    (hcut : PrefixKernelConeOneStepCutAt D W eps rho mu hsc q) :
    ∀ (lam : Lambda) (n : ℕ),
      (((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n).Finite := by
  obtain ⟨radius, hradius⟩ := hcut
  intro lam n
  let E := (D.adjoinRelatorPrefixes W
    hsc.toIsSmallCancellation).adjoinKernel q
  have hfinite : ∀ m : ℕ, (E.relBall lam m).Finite := by
    intro m
    induction m with
    | zero =>
        have hsource : (D.relBall lam (radius 0)).Finite :=
          hD.locallyFinite lam (radius 0)
        have hsub : E.relBall lam 0 ⊆ D.relBall lam (radius 0) := by
          intro y hy
          obtain hsourceY | hnext := hradius lam 0 y hy
          · exact hsourceY
          · exact (Nat.not_lt_zero _ hnext.1).elim
        exact hsource.subset hsub
    | succ m ihm =>
        have hsource : (D.relBall lam (radius (m + 1))).Finite :=
          hD.locallyFinite lam (radius (m + 1))
        have hprev : (E.relBall lam m).Finite := ihm
        have hsub : E.relBall lam (m + 1) ⊆
            D.relBall lam (radius (m + 1)) ∪ E.relBall lam m := by
          intro y hy
          obtain hsourceY | hnext := hradius lam (m + 1) y hy
          · exact Set.mem_union_left _ hsourceY
          · have hmn : m + 1 - 1 = m := by omega
            have hprevY : y ∈ E.relBall lam m := by
              rw [← hmn]
              exact hnext.2
            exact Set.mem_union_right _ hprevY
        exact (hsource.union hprev).subset hsub
  exact hfinite n

/-- The pointwise cone embeddedness conclusion obtained from the proved
kernel-geodesic estimate and the relative-ball induction. -/
theorem isHyperbolicallyEmbedded_prefixKernelCone_of_kernelEstimate_and_oneStepCuts
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q)
    (hkernel : KernelGeodesicEstimateAt D W eps rho mu hsc q)
    (hcut : PrefixKernelConeOneStepCutAt D W eps rho mu hsc q) :
    ((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).IsHyperbolicallyEmbedded := by
  obtain ⟨M, hM⟩ := hkernel
  have hfinite := locallyFinite_prefixKernelCone_of_oneStepCuts D hD W hsc q
    hcut
  exact isHyperbolicallyEmbedded_prefixKernelCone_of_bounds D hD W hsc q M hM
    hfinite

/-- The one-point source satisfies the cut premise with source radius zero
exactly: every cone-ball element is the unique group element. -/
theorem prefixKernelConeOneStepCutAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : PUnit →* Q) :
    PrefixKernelConeOneStepCutAt D W eps rho mu hsc q := by
  refine ⟨fun _ => 0, ?_⟩
  intro lam n y hy
  left
  rw [GGT.RelGenSet.relBall_zero]
  exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

end HullSC
end GroupApproximation
