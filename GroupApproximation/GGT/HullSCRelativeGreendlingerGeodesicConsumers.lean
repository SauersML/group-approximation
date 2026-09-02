import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity

/-!
# Consumers of relative Greendlinger at the length-only boundary hypothesis

`HullSCRelativeGreendlingerSpelling` proves
`RelativeGreendlingerGeodesicLengthStatement` from est's three construction
propositions, the vk realization at a supplied admissible spelling, and the
supplied-word arc conversion.  Its boundary hypothesis,
`RelativeReducedDiagram.HasGeodesicBoundaryLength`, is about lengths only.

This module spends that statement at the consumers.  The point is that the
hypothesis is **discharged**, not carried: every diagram reaching
`HullSC.injOn_relativeBall_of_relativeDiagramCertificates` and
`HullSC.exists_relativeBallInjectivityParameters_of_greendlinger` is
`Z.toRelativeReducedDiagram D` for a `Lemma44OrientedRelatorDiagram`, and
`hasGeodesicBoundaryLength_toRelativeReducedDiagram` supplies the hypothesis
for such a diagram with no side condition.

So `AllReducedDiagramsHaveBaseGeodesicBoundary`, the residue of
`HullSCRelativeGreendlingerFromComponents` that cannot be discharged, does not
appear anywhere below.  Relative-ball injectivity now follows from est's three
propositions and the two vk-side residues alone.

Every declaration below is a complete proof; no placeholder of any kind is
introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Ball injectivity at fixed parameters -/

/-- **Ball injectivity from certificates at geodesic-boundary diagrams
only.**  This is `injOn_relativeBall_of_relativeDiagramCertificates` with the
certificate family restricted to diagrams satisfying
`HasGeodesicBoundaryLength`.  The restriction costs nothing: the diagram the
proof produces is a Hull Lemma 4.4 diagram, whose geodesic boundary length is
the field the coercion discards. -/
theorem injOn_relativeBall_of_geodesicLengthCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeReducedDiagram D W R,
      Z.HasGeodesicBoundaryLength →
        Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    Set.InjOn q (cayleyBall D.alphabet R) := by
  by_contra hnot
  obtain ⟨Z0⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    D.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z0.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨K⟩ := hcert (Z.toRelativeReducedDiagram D)
    (hasGeodesicBoundaryLength_toRelativeReducedDiagram D Z)
  exact false_of_relativeDiagramCertificate D Z hsc hmu hthreshold K

/-! ## Parameters for an arbitrary relative ball -/

/-- **The drop-in replacement for
`exists_relativeBallInjectivityParameters_of_greendlinger`.**  Its hypothesis
is the length-only restricted statement instead of the unrestricted one; the
conclusion is identical, so every consumer built on that theorem transfers
unchanged.  The numerical choices are the ones the original makes. -/
theorem exists_relativeBallInjectivityParameters_of_geodesicLengthGreendlinger
    (hgeom : RelativeGreendlingerGeodesicLengthStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall D.alphabet R) := by
  let mu : ℝ := 1 / 100
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  obtain ⟨eps, rho0, hgood⟩ := hgeom D hemb mu hmuPos hmuSixteen
  let boundaryScale : ℕ := 2 * R + 2 * eps + 1
  let rho : ℕ := max rho0 (8 * boundaryScale)
  have hrho0 : rho0 ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho := Nat.le_max_right _ _
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale]
    positivity
  have hrhoScaleReal : (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hker
  exact injOn_relativeBall_of_geodesicLengthCertificates D hsc hmuNinetyTwo
    hthreshold q hker (fun Z hZ => hgood rho hrho0 W R hsc Z hZ)

/-! ## The composite, with no boundary universality -/

/-- **Relative-ball injectivity from the estimating components alone.**

The hypotheses are est's three construction propositions and the two vk-side
residues.  `AllReducedDiagramsHaveBaseGeodesicBoundary` does not appear, and
neither does any hypothesis about the boundary word of an arbitrary reduced
diagram: the boundary geometry is supplied, where it is needed, by the Hull
Lemma 4.4 diagram itself. -/
theorem exists_relativeBallInjectivityParameters_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall D.alphabet R) :=
  exists_relativeBallInjectivityParameters_of_geodesicLengthGreendlinger
    (relativeGreendlingerGeodesicLengthStatement_of_components
      hselection hpieces hunbound hreal hconv)
    D hemb R

/-! ## The unrestricted statement still implies the restricted one -/

/-- The length-only statement is weaker than the unrestricted one, so a future
proof of `RelativeGreendlingerStatement` also serves every consumer below. -/
theorem relativeGreendlingerGeodesicLengthStatement_of_relativeGreendlingerStatement
    (h : RelativeGreendlingerStatement.{u, w}) :
    RelativeGreendlingerGeodesicLengthStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps, rho0, hgood⟩ := h D hD mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hinput Z _
  exact hgood rho hrho W R hinput Z

end HullSC
end GroupApproximation
