import GroupApproximation.GGT.HullSCLemma44BoundedFamilyBridge
import GroupApproximation.GGT.HullSCLeastAreaGreendlingerTwins
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 4.4 family form at the least-area Greendlinger waist

`boundedFamilyInclusionRelativeEmbeddingStatement_of_quasiGeodesic_of_respelling`
(`GGT/HullSCLemma44BoundedFamilyBridge.lean`) takes Osin's Lemma 4.4 in
certificate form at every reduced diagram with a quasi-geodesic spelling.  Osin's
Lemma 4.4 is about least-area diagrams, and the embedded bridge
`RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` asks for no more, so
this module restates the producer with the least-area waist
`RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement`
(`GGT/HullSCLeastAreaGreendlingerTwins.lean`).  Every numerical choice is the
original's.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **The two auxiliary embeddings of the family form, from the least-area
certificate theorem, the embedded bridge and a bounded re-spelling.**
`boundedFamilyInclusionRelativeEmbeddingStatement_of_quasiGeodesic_of_respelling`
with the least-area waist in place of the reduced-diagram waist. -/
theorem boundedFamilyInclusionRelativeEmbeddingStatement_of_leastAreaQuasiGeodesic_of_respelling
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement.{u, w})
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
    exact hbridge original horiginal epsO rho' mu W' q hq hmuPos hmuThousand
      h20 hscO hkerO
      (fun R Z hZ => hcertO rho' hrhoO W' R hscO.toIsLemma44Input Z hZ)
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
    exact hbridge joint hjoint epsJ rho' mu W' q hq hmuPos hmuThousand
      h20 hscJ hkerJ
      (fun R Z hZ => hcertJ rho' hrhoJ W' R hscJ.toIsLemma44Input Z hZ)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.boundedFamilyInclusionRelativeEmbeddingStatement_of_leastAreaQuasiGeodesic_of_respelling
