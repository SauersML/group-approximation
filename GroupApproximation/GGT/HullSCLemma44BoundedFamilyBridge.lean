import GroupApproximation.GGT.HullSCLemma44BoundedBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 4.4 family form over strongly bounded relator families

The combinators of `GGT/HullSCLemma44QuasiGeodesicBridge.lean` and
`GGT/HullSCLemma44FamilyAssembly.lean` for the family form, restated over
`RelWord.IsBoundedLemma44Input` and against the embedded bridge
`RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`.  Every numerical
choice is the original's.

`BoundedHullRelatorRespellingStatement` is used here only as a hypothesis of a
true implication.  It is not a leaf of Theorem C: the uniform re-spelling over
every family is not a statement of Osin or of Hull, and the chain to
Fournier-Facio's Proposition 2.3 goes through the published relator instead.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **The two auxiliary embeddings of the family form, from the certificate
theorem, the embedded bridge and a bounded re-spelling.**
`familyInclusionRelativeControlStatement_of_quasiGeodesic_of_respelling` with the
bounded input and the embedded conclusion. -/
theorem boundedFamilyInclusionRelativeEmbeddingStatement_of_quasiGeodesic_of_respelling
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, u, w})
    (hrespell : BoundedHullRelatorRespellingStatement.{u, w}) :
    BoundedFamilyInclusionRelativeEmbeddingStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint hA horiginal hjoint hinl hinr
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨epsO, rho0O, hcertO⟩ :=
    hgeom original horiginal mu hmuPos hmuSixteen
  obtain ⟨epsJ, rho0J, hcertJ⟩ := hgeom joint hjoint mu hmuPos hmuSixteen
  obtain ⟨epsS, rhoS, hres⟩ :=
    hrespell selected original joint hA horiginal hjoint hinl hinr mu hmuPos
      hmuThousand (max epsO epsJ) (max rho0O rho0J)
  refine ⟨epsS, rhoS, mu, hmuPos, ?_⟩
  intro W Q _ q hq hsc hker
  obtain ⟨hrespO, hrespJ⟩ := hres W hsc
  constructor
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespO
    have hepsO : epsO ≤ eps' := le_trans (Nat.le_max_left _ _) heps'
    have hrhoO : rho0O ≤ rho' := le_trans (Nat.le_max_left _ _) hrho'
    have hscO : RelWord.IsBoundedLemma44Input original W' epsO mu rho' :=
      hsc'.mono_parameters hepsO le_rfl le_rfl
    have hkerO : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsO + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsO + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram original W' R),
        Z.HasQuasiGeodesicSpelling →
          Nonempty (RelativeDiagramCertificate original W' epsO mu Z) := by
      intro R Z hZ
      exact hcertO rho' hrhoO W' R hscO.toIsLemma44Input Z hZ
    exact hbridge original horiginal epsO rho' mu W' q hq hmuPos hmuThousand
      h20 hscO hkerO hcert
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespJ
    have hepsJ : epsJ ≤ eps' := le_trans (Nat.le_max_right _ _) heps'
    have hrhoJ : rho0J ≤ rho' := le_trans (Nat.le_max_right _ _) hrho'
    have hscJ : RelWord.IsBoundedLemma44Input joint W' epsJ mu rho' :=
      hsc'.mono_parameters hepsJ le_rfl le_rfl
    have hkerJ : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsJ + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsJ + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram joint W' R),
        Z.HasQuasiGeodesicSpelling →
          Nonempty (RelativeDiagramCertificate joint W' epsJ mu Z) := by
      intro R Z hZ
      exact hcertJ rho' hrhoJ W' R hscJ.toIsLemma44Input Z hZ
    exact hbridge joint hjoint epsJ rho' mu W' q hq hmuPos hmuThousand
      h20 hscJ hkerJ hcert

/-- **The bounded repaired family form from the bounded canonical statement and
the two auxiliary embeddings.**
`hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls`
with the bounded input, reading embeddedness where the original read control. -/
theorem boundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_embeddings
    (h44 : BoundedHullLemma44CanonicalQuotientStatement.{u})
    (hemb : BoundedFamilyInclusionRelativeEmbeddingStatement.{u, w}) :
    BoundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal joint hbaseInv
    hjointOriginal hjointSelected hjointEmbedded hjointSub R
  obtain ⟨epsP, rhoP, muP, hmuP, hgood⟩ := h44 selected (max R 1)
  obtain ⟨epsC, rhoC, muC, hmuC, hcontrol⟩ :=
    hemb selected original joint hA horiginal hjointEmbedded hjointOriginal
      hjointSelected
  refine ⟨max epsP epsC, max rhoP rhoC, min muP muC, lt_min hmuP hmuC, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hscP : RelWord.IsBoundedLemma44Input selected.rel W epsP muP rhoP :=
    hsc.mono_parameters (Nat.le_max_left _ _) (min_le_left _ _)
      (Nat.le_max_left _ _)
  have hscC : RelWord.IsBoundedLemma44Input selected.rel W epsC muC rhoC :=
    hsc.mono_parameters (Nat.le_max_right _ _) (min_le_right _ _)
      (Nat.le_max_right _ _)
  obtain ⟨hinjMax, hselectedPreserved⟩ := hgood W q hscP hsurj hker
  have hinjR : Set.InjOn q (cayleyBall A.alphabet R) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_left R 1))
  have hinjOne : Set.InjOn q (cayleyBall A.alphabet 1) :=
    hinjMax.mono
      (cayleyBall_subset_of_le_radius A.alphabet (Nat.le_max_right R 1))
  obtain ⟨horiginalEmbedded, hjointQ⟩ := hcontrol W q hsurj hscC hker
  have horiginalUnion : Set.InjOn q
      (⋃ lam : Lambda, (original.fam lam : Set G)) := by
    intro x hx y hy hxy
    exact hinjOne
      (originalPeripheralUnion_subset_cayleyBall_one original hA hx)
      (originalPeripheralUnion_subset_cayleyBall_one original hA hy) hxy
  exact ⟨hinjR, hselectedPreserved,
    canonicalQuotientFamilyPreservation_of_embedded original q hsurj
      horiginalEmbedded horiginalUnion selected.rel.alphabet.carrier,
    quotientJointPeripheralPreservation_of_embedded selected original joint
      hbaseInv hjointOriginal hjointSelected q hsurj hjointSub hjointQ⟩

/-- The bounded family form from the bounded repaired form and the joint-family
selection input: `hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint`
over bounded families. -/
theorem boundedHullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (hsel : JointAuxiliaryPeripheralEmbedding.{u, w})
    (h44 : BoundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    BoundedHullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} := by
  intro G _ A N k S selected Lambda original hA horiginal R
  obtain ⟨joint, hbaseInv, hjointOriginal, hjointSelected, hjointEmbedded,
    hjointSub⟩ := hsel selected original hA horiginal
  exact h44 selected original hA horiginal joint hbaseInv hjointOriginal
    hjointSelected hjointEmbedded hjointSub R

/-- The bounded family form from Dahmani--Guirardel--Osin's Proposition 4.14 and
the bounded repaired form. -/
theorem boundedHullLemma44CanonicalQuotientFamilyInclusionStatement_of_proposition414Uniform
    (h414 : GGT.OsinComponents.DGOProposition414Uniform.{u, 0})
    (h44 : BoundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    BoundedHullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} :=
  boundedHullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (jointAuxiliaryPeripheralEmbedding_of_proposition414Uniform h414) h44

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.boundedFamilyInclusionRelativeEmbeddingStatement_of_quasiGeodesic_of_respelling
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_embeddings
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientFamilyInclusionStatement_of_proposition414Uniform
