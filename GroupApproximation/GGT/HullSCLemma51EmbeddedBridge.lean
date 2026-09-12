import GroupApproximation.GGT.HullSCLemma51QuasiGeodesicTransfer
import GroupApproximation.GGT.HullSCLemma44BoundedInput
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 5.1 bridge in the form its consumers read

`RelativeIsoperimetricBridgeQuasiGeodesicStatement`
(`GGT/HullSCLemma44QuasiGeodesicBridge.lean`), one of the four Hull leaves of
Theorem C, concludes `RelativeIsoperimetricControl`, and it quantifies over
every family satisfying `RelWord.IsLemma44Input`.  Both choices ask for more
than Osin's Lemma 5.1 gives and more than anything consumes.

## What the consumers read

Every consumer of `RelativeIsoperimetricControl` on main reads only
`RelativeIsoperimetricControl.embedded`, i.e. hyperbolic embeddedness of the
image family `D.mapSurjective q hq`:
`quotientPeripheralPreservation_of_isoperimetricControl`,
`canonicalQuotientFamilyPreservation_of_control` and
`quotientJointPeripheralPreservation_of_control`.  The `peripheralPullback`
clause (quotient relative balls inside images of *source* relative balls) is
never read, and it is not what Osin proves: when a relator carries a peripheral
letter `h` whose source relative distance is infinite, the complementary arc of
the relator reaches `q h` in the quotient by a path of base letters.  The header
of `GGT/HullSCLemma44BoundedInput.lean` records the same defect.

## The length bound

Osin's Lemma 5.1 is stated for a **finite** symmetrized family, and Hull's
strongly bounded families have uniformly bounded relator lengths.
`IsLemma44Input` records only finite peripheral support; `IsBoundedLemma44Input`
restores the bound.  Without it the conclusion fails for infinite
small-cancellation families of unbounded length over a free group, whose
quotients are infinitely presented and so not hyperbolic; and the unbounded area
transfer is refuted outright (`not_relativeLinearAreaTransferStatement`).

## What is proved here

* `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` — the leaf with the
  bounded input and the embedded conclusion;
* `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_quasiGeodesicBridge`
  — the printed leaf implies it, so it is no stronger than what the assembly
  admits;
* `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer`
  — it follows from `BoundedRelativeLinearAreaTransferStatement` alone, through
  the linear relative area of
  `relativeLinearKernelArea_of_quasiGeodesicCertificates`.  That transfer —
  a linear relative isoperimetric inequality over strongly bounded relators gives
  hyperbolic embeddedness of the image family — is the residue of the leaf;
* `quotientPeripheralPreservation_of_embeddedBridge` — the consumer, at the
  embedded bridge.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u v w

/-- **Osin's Lemma 5.1, pointwise, in the form its consumers read.**  The
certificate hypothesis is asked only at diagrams with a quasi-geodesic spelling,
the relator family is strongly bounded in Hull's published sense, and the
conclusion is hyperbolic embeddedness of the image family. -/
def RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (eps rho : ℕ) (mu : ℝ)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {Q : Type v} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q),
    0 < mu → mu ≤ 1 / 1000 →
      20 * (eps + 1) ≤ rho →
      RelWord.IsBoundedLemma44Input D W eps mu rho →
      q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
        (∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
          Z.HasQuasiGeodesicSpelling →
            Nonempty (RelativeDiagramCertificate D W eps mu Z)) →
            (D.mapSurjective q hq).IsHyperbolicallyEmbedded

/-- Uniform form over all hyperbolically embedded source relative generating
sets. -/
def RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedAt.{u, v, w} D

/-- **The printed leaf implies the embedded bridge.**  Bounded inputs are inputs,
and control gives embeddedness. -/
theorem relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_quasiGeodesicBridge
    (h : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, v, w}) :
    RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, v, w} := by
  intro G _ Lambda D hD eps rho mu W Q _ q hq hmu hmuUpper hrho hsc hker hcert
  obtain ⟨C⟩ := h D hD eps rho mu W q hq hmu hmuUpper hrho hsc.toIsLemma44Input
    hker hcert
  exact C.embedded hD

/-- A relator family spelling kernel values is killed by the quotient. -/
theorem map_listVal_eq_one_of_ker_eq_normalClosure
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    ∀ word ∈ W, q (GGT.RelLetter.listVal word) = 1 := by
  intro word hword
  have hmem : GGT.RelLetter.listVal word ∈ q.ker := by
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨word, hword, rfl⟩
  exact MonoidHom.mem_ker.mp hmem

/-- **The embedded bridge from the bounded relative-area transfer.**  The
restricted certificates give linear relative area by Osin's induction
(`relativeLinearKernelArea_of_quasiGeodesicCertificates`), and the bounded
transfer turns linear area over a strongly bounded family into hyperbolic
embeddedness of the image family. -/
theorem relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer
    (htransfer : BoundedRelativeLinearAreaTransferStatement.{u, v, w}) :
    RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, v, w} := by
  intro G _ Lambda D hD eps rho mu W Q _ q hq _hmu hmuUpper hrho hsc hker hcert
  exact htransfer D hD W q hq hsc.admissible hsc.isStronglyBounded
    (map_listVal_eq_one_of_ker_eq_normalClosure q hker)
    (relativeLinearKernelArea_of_quasiGeodesicCertificates D hsc.toIsLemma44Input
      hmuUpper hrho q hker hcert)

/-- **Hull's peripheral preservation at the embedded bridge.**  This is
`quotientPeripheralPreservation_of_quasiGeodesicCertificates` with the bounded
input and the embedded bridge; its proof reads nothing but embeddedness. -/
theorem quotientPeripheralPreservation_of_embeddedBridge
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, u, 0})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {eps rho : ℕ} {mu : ℝ}
    {W : Set (List
      (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (hsc : RelWord.IsBoundedLemma44Input D.rel W eps mu rho)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D.rel W eps mu Z))
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) :=
  quotientPeripheralPreservation_of_mapSurjective D q hq
    (hbridge D.rel D.embedded eps rho mu W q hq hmu hmuUpper hrho hsc hker
      hcert) hinj

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_quasiGeodesicBridge
#audit_axioms GroupApproximation.HullSC.map_listVal_eq_one_of_ker_eq_normalClosure
#audit_axioms GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer
#audit_axioms GroupApproximation.HullSC.quotientPeripheralPreservation_of_embeddedBridge
