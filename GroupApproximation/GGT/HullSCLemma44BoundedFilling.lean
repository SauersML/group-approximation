import GroupApproximation.GGT.HullSCLemma44BoundedInput
import GroupApproximation.GGT.HullSCLemma44Canonical

/-!
# Hull's bounded filling conclusion from its two geometric inputs

The published boundedness condition reaches the actual quotient geometry in
this reduction. It uses neither the refuted unbounded area-transfer statement
nor the excessive original-relative-ball pullback certificate. The remaining
inputs are explicitly the relative Greendlinger theorem and the bounded
relative-presentation transfer. Neither is claimed to be proved here.
-/

namespace GroupApproximation.HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-- Hull Lemma 4.4 at its published bounded input, retaining relative-ball
injectivity and hyperbolic embeddedness over the image of the source base. -/
def BoundedRelativeFillingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → ∀ R : ℕ,
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ))) {Q : Type v} [Group Q]
          (q : G →* Q) (hq : Function.Surjective q),
          RelWord.IsBoundedLemma44Input D W eps mu rho →
          q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
            Set.InjOn q (cayleyBall D.alphabet R) ∧
              (D.mapSurjective q hq).IsHyperbolicallyEmbedded

/-- The bounded transfer applies to the area produced by the existing
boundary-length induction. Relator killing follows from the kernel equation. -/
theorem embedded_of_bounded_transfer_of_certificates
    (htransfer : BoundedRelativeLinearAreaTransferStatement.{u, v, w})
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    (hD : D.IsHyperbolicallyEmbedded)
    {W : Set (List (GGT.RelLetter G Λ))} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsBoundedLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    {Q : Type v} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded := by
  apply htransfer D hD W q hq hsc.admissible hsc.isStronglyBounded
  · intro word hword
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨word, hword, rfl⟩
  · exact relativeLinearKernelArea_of_certificates D hsc.toIsLemma44Input
      hmu hrho q hker hcert

/-- The source-faithful bounded filling reduction. Both constants and
conclusions use the same source relative alphabet and the same quotient. -/
theorem boundedRelativeFilling_of_greendlinger_of_boundedTransfer
    (hgeom : RelativeGreendlingerStatement.{u, w})
    (htransfer : BoundedRelativeLinearAreaTransferStatement.{u, v, w}) :
    BoundedRelativeFillingStatement.{u, v, w} := by
  intro G _ Λ D hD R
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by norm_num [mu]
  have hmuSixteen : mu ≤ 1 / 16 := by norm_num [mu]
  have hmuNinetyTwo : mu ≤ 1 / 92 := by norm_num [mu]
  obtain ⟨eps, rho₀, hcertificate⟩ := hgeom D hD mu hmuPos hmuSixteen
  let scale := 2 * R + 2 * eps + 1
  let rho := max rho₀ (max (8 * scale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * scale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hscalePos : (0 : ℝ) < (scale : ℝ) := by dsimp [scale]; positivity
  have hrhoReal : (8 : ℝ) * (scale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) < (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (scale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hq hsc hker
  have hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D W r),
      Nonempty (RelativeDiagramCertificate D W eps mu Z) := by
    intro r Z
    exact hcertificate rho hrho₀ W r hsc.toIsLemma44Input Z
  refine ⟨injOn_relativeBall_of_relativeDiagramCertificates D
    hsc.toIsLemma44Input hmuNinetyTwo hthreshold q hker (hcert R), ?_⟩
  exact embedded_of_bounded_transfer_of_certificates htransfer D hD hsc
    le_rfl hrhoDehn q hq hker hcert

end GroupApproximation.HullSC

#audit_axioms GroupApproximation.HullSC.embedded_of_bounded_transfer_of_certificates
#audit_axioms GroupApproximation.HullSC.boundedRelativeFilling_of_greendlinger_of_boundedTransfer
