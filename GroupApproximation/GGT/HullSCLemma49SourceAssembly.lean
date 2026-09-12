import GroupApproximation.GGT.HullSCLemma49SourceBranches
import GroupApproximation.GGT.HullSCLemma49BowditchGap
import GroupApproximation.GGT.HullSCLemma49ShortPower
import GroupApproximation.GGT.HullSCLemma49FacePasting
import GroupApproximation.GGT.HullSCLemma49InjectivityBridge

/-!
# Assembly of the source-faithful Lemma 4.9 branches

This module synchronizes the three cases in Hull's proof of Lemma 4.9.  The
long-period and bounded-loxodromic cases use the source quasi-geodesic
Greendlinger statement and the cellular boundary-value handoff.  The remaining
non-loxodromic case uses the ball-injectivity consequence of the same
small-cancellation data, supplied by the Lemma 4.4 lane.  The output is the
shortest-geodesic power-diagram statement, so a quotient-free kernel statement
can be obtained by the theorem in `HullSCLemma49PowerDiagram`.

The numerical choices are made after all three preliminary constants are
known.  Increasing `eps` and `rho`, and decreasing `mu`, preserves the input
condition by its monotonicity theorem.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The common coefficient -/

/-- The common coefficient of the three branches is positive. -/
theorem sourceLemma49_commonMu_pos {muShort muInjective : ℝ}
    (hshort : 0 < muShort) (hinjective : 0 < muInjective) :
    0 < min (1 / 100000 : ℝ) (min muShort muInjective) := by
  rw [lt_min_iff, lt_min_iff]
  exact ⟨by norm_num, hshort, hinjective⟩

/-- The common coefficient is no larger than the long-period coefficient. -/
theorem sourceLemma49_commonMu_le_long (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ 1 / 100000 :=
  min_le_left _ _

/-- The common coefficient is no larger than the bounded-loxodromic one. -/
theorem sourceLemma49_commonMu_le_short (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muShort := by
  exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- The common coefficient is no larger than the injectivity one. -/
theorem sourceLemma49_commonMu_le_injective (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muInjective := by
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The four numerical facts needed after synchronizing the branches. -/
theorem sourceLemma49_commonMu_bounds {muShort muInjective : ℝ}
    (hshort : 0 < muShort) (hinjective : 0 < muInjective) :
    0 < min (1 / 100000 : ℝ) (min muShort muInjective) ∧
      min (1 / 100000 : ℝ) (min muShort muInjective) ≤ 1 / 100000 ∧
      min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muShort ∧
      min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muInjective := by
  exact ⟨sourceLemma49_commonMu_pos hshort hinjective,
    sourceLemma49_commonMu_le_long muShort muInjective,
    sourceLemma49_commonMu_le_short muShort muInjective,
    sourceLemma49_commonMu_le_injective muShort muInjective⟩

/-- The middle entry is bounded by the nested maximum used for parameters. -/
theorem sourceLemma49_middle_le_nestedMax (a b c : ℕ) :
    b ≤ max a (max b c) := by
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The last entry is bounded by the nested maximum used for parameters. -/
theorem sourceLemma49_last_le_nestedMax (a b c : ℕ) :
    c ≤ max a (max b c) := by
  exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The complement of the long-period alternative is the integral short-period
bound used by Hull's bounded branch. -/
theorem sourceLemma49_shortPeriod_of_not_long
    {delta length : ℕ} (hnot : ¬ 8 * delta + 2 ≤ length) :
    length ≤ 8 * delta + 1 := by
  omega

/-! ## The three-case assembly -/

/-- The source Greendlinger branches and ball injectivity imply Hull's exact
shortest-geodesic power-diagram statement.  The argument is Hull's Lemma 4.9:
the first two cases contradict the selected long cell, while in the last case
a shortest conjugate of the non-loxodromic power lies in the protected ball. -/
theorem hullLemma49ShortestGeodesicPowerDiagram_of_sourceBranches
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    (hpasting : HullLemma49SourceFacePastingStatement.{u, w})
    (hinjective : HullLemma49InjectivityCallback.{u, w}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{u, w} := by
  intro G _ Lambda _ D hemb hacylindrical
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  have hgap : CayleyUniformLoxodromicTranslationGap D.alphabet :=
    cayleyUniformLoxodromicTranslationGap_of_hyperbolicallyEmbedded
      D hemb hacylindrical
  obtain ⟨epsLong, rhoLong, hlong⟩ :=
    exists_parameters_false_of_longPeriod_powerDiagram_source
      hgeom D hdelta hpasting
  obtain ⟨epsShort, rhoShort, muShort, hmuShort, _hmuShortUpper,
      hshortLox⟩ :=
    exists_parameters_false_of_shortLoxodromic_powerDiagram_source
      hgeom D hdelta hgap hpasting
  obtain ⟨epsInjective, rhoInjective, muInjective, hmuInjective,
      hinjAll⟩ := hinjective D hemb delta hdelta
  let eps : ℕ := max epsLong (max epsShort epsInjective)
  let rho : ℕ := max rhoLong (max rhoShort rhoInjective)
  let mu : ℝ := min (1 / 100000 : ℝ) (min muShort muInjective)
  have hcommon := sourceLemma49_commonMu_bounds hmuShort hmuInjective
  have hmu : 0 < mu := by
    dsimp [mu]
    exact hcommon.1
  have hepsLong : epsLong ≤ eps := Nat.le_max_left _ _
  have hepsShort : epsShort ≤ eps :=
    sourceLemma49_middle_le_nestedMax epsLong epsShort epsInjective
  have hepsInjective : epsInjective ≤ eps :=
    sourceLemma49_last_le_nestedMax epsLong epsShort epsInjective
  have hrhoLong : rhoLong ≤ rho := Nat.le_max_left _ _
  have hrhoShort : rhoShort ≤ rho :=
    sourceLemma49_middle_le_nestedMax rhoLong rhoShort rhoInjective
  have hrhoInjective : rhoInjective ≤ rho :=
    sourceLemma49_last_le_nestedMax rhoLong rhoShort rhoInjective
  have hmuLong : mu ≤ (1 / 100000 : ℝ) := by
    dsimp [mu]
    exact hcommon.2.1
  have hmuShort' : mu ≤ muShort := by
    dsimp [mu]
    exact hcommon.2.2.1
  have hmuInjective' : mu ≤ muInjective := by
    dsimp [mu]
    exact hcommon.2.2.2
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hshort Z
  have hlongInput : RelWord.IsLemma49Input D W epsLong
      (1 / 100000) rhoLong :=
    hinput.mono_parameters hepsLong hmuLong hrhoLong
  have hshortInput : RelWord.IsLemma49Input D W epsShort
      muShort rhoShort :=
    hinput.mono_parameters hepsShort hmuShort' hrhoShort
  by_cases hlox : IsLoxodromic g (Cayley.base D.alphabet)
  · by_cases hperiodLong : 8 * delta + 2 ≤ Z.boundaryWord.length
    · exact (hlong W v hv hlongInput g n hshort Z hperiodLong).elim
    · have hperiodShort : Z.boundaryWord.length ≤ 8 * delta + 1 := by
        exact sourceLemma49_shortPeriod_of_not_long hperiodLong
      exact (hshortLox W v hv hshortInput g n hshort hlox Z hperiodShort).elim
  · let N : Subgroup G :=
      Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
    letI : N.Normal := Subgroup.normalClosure_normal
    let quotientMap : G →* G ⧸ N := QuotientGroup.mk' N
    have hsymInput : RelWord.IsLemma49Input D
        (RelWord.symmetrized v) eps mu rho := hinput.restrict_symmetrized hv
    have hinjectiveInput : RelWord.IsLemma49Input D
        (RelWord.symmetrized v) epsInjective muInjective rhoInjective :=
      (hsymInput.mono_parameters hepsInjective hmuInjective'
        hrhoInjective)
    have hker : quotientMap.ker =
        Subgroup.normalClosure
          (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
      dsimp [quotientMap]
      rw [QuotientGroup.ker_mk',
        RelWord.normalClosure_listVal_image_symmetrized]
    have hinjBall : Set.InjOn quotientMap
        (cayleyBall D.alphabet (8 * delta + 1)) := by
      apply hinjAll (W := RelWord.symmetrized v) (q := quotientMap)
      · exact hinjectiveInput
      · exact hker
    exact (false_of_powerDiagram_of_not_isLoxodromic_of_ballInjective
      D Z hdelta hlox hinjBall).elim

/-! ## Model check -/

/-- The trivial-group model has no nontrivial power diagram, so the assembled
conclusion is vacuous in that model. -/
theorem sourceLemma49Assembly_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (v : List (GGT.RelLetter PUnit Lambda)) (n : ℕ) :
    Lemma49GeodesicPowerDiagram D v 1 n →
      ∃ k ∈ Subgroup.normalClosure
          ({GGT.RelLetter.listVal v} : Set PUnit),
        (1 * k) ^ n = 1 := by
  intro Z
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
