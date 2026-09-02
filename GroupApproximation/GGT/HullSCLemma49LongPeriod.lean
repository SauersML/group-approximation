import GroupApproximation.GGT.HullSCLemma49PrimePiece

/-!
# Hull's Lemma 4.9 for a long shortest period

This module assembles the shared relative Greendlinger certificate, the
periodic boundary decomposition, the quadrangle shadow, and the prime-piece
contradiction.  It proves the loxodromic-length branch of Hull's Lemma 4.9:
no nontrivial reduced power diagram exists when the shortest period has length
at least `8 * delta + 2`.

The parameter order follows Osin's proof of Lemma 6.3.  Relative
Greendlinger first chooses `eps`.  Hyperbolicity and `eps` then choose the
shadow constant.  The final `C₁` parameter enlarges `eps`, lowers `mu` to
`1/100000`, and enlarges `rho`.  Monotonicity supplies the certificate at
`mu = 1/1000`, while the stronger prime-piece estimate is retained at the
smaller final value.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u w

/-- The prime-piece scale used in the long-arc branch also dominates the
short-arc scale required to rule out the two shortening alternatives. -/
theorem lemma49_shorteningScale_le_of_primePieceScale
    {eps b K rho : ℕ}
    (hscale : 1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ rho) :
    100 * (2 * eps + 1) ≤ rho := by
  omega

/-- Once the shared Greendlinger cell and its quadrangle shadow have been
selected, the long-period branch is impossible.  The short exposed-arc cases
contradict quotient-conjugacy minimality; the remaining long arc supplies two
large prime pieces in one cyclic relator. -/
theorem false_of_longPeriod_powerDiagram_of_cell
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    {eps epsFinal rho delta K : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (Sh : Lemma49ContiguityShadow C K)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier
      (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) g)
    (hcertificateInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hfinalInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsFinal (1 / 100000) rho)
    (hscale :
      1000 * (4 * (8 * delta + 2) + 24 * K + 18 * eps + 18) ≤ rho)
    (hconnectors : 2 * K ≤ epsFinal)
    (hlongPeriod : 8 * delta + 2 ≤ Z.boundaryWord.length) : False := by
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  letI : N.Normal := Subgroup.normalClosure_normal
  have hshortScale : 100 * (2 * eps + 1) ≤ rho :=
    lemma49_shorteningScale_le_of_primePieceScale hscale
  have hlongArc : 4 * Z.boundaryWord.length ≤
      3 * C.boundaryArc.length :=
    four_mul_period_le_three_mul_arc C hcertificateInput hshortScale hshort
  have hwordNe : Z.boundaryWord ≠ [] := by
    intro hnil
    have hg : g = 1 := by
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa using Z.boundary_geodesic.2.1
      rw [hnil] at hvalue
      calc
        g = GGT.RelLetter.listVal
            ([] : List (GGT.RelLetter G Lambda)) := hvalue.symm
        _ = 1 := GGT.RelLetter.listVal_nil
    exact Z.power_ne_one (by simp [hg])
  have hperiodPos : 0 < Z.boundaryWord.length :=
    List.length_pos_iff.mpr hwordNe
  have harcInfix : C.boundaryArc <:+:
      lemma49BoundaryPower Z.boundaryWord n :=
    ⟨C.boundaryBefore, C.boundaryAfter, C.boundary_decomposition.symm⟩
  obtain ⟨B⟩ := exists_repeatedBoundaryBlocks_of_lemma49PowerArc
    Z.exponent_pos harcInfix hperiodPos hlongArc
  have hPowerGlobal := isQuasiGeodesicChainAt_power_of_long_period
    D N hshort Z.boundary_geodesic Z.exponent_pos hdelta hlongPeriod
  have hPower := C.powerArc_isQuasiGeodesicChainAt hPowerGlobal
  have hRel := C.exterior_isQuasiGeodesicChainAt hcertificateInput
  exact false_of_lemma49LongArc_contiguityShadow C B Sh hcertificateInput
    hfinalInput hRel hPower hscale hconnectors

/-- The single shared Greendlinger proposition rules out every long-period
nontrivial power diagram. -/
theorem exists_parameters_false_of_longPeriod_powerDiagram
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ (eps rho delta : ℕ),
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        (v : List (GGT.RelLetter G Lambda)), v ∈ W →
        RelWord.IsLemma49Input D W eps (1 / 100000) rho →
          ∀ (g : G) (n : ℕ),
            IsShortestModuloConjugacy D.alphabet.carrier
              (Subgroup.normalClosure
                ({GGT.RelLetter.listVal v} : Set G)) g →
            ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
              8 * delta + 2 ≤ Z.boundaryWord.length → False := by
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  have hmuCertPos : (0 : ℝ) < 1 / 1000 := by norm_num
  have hmuCertUpper : (1 / 1000 : ℝ) ≤ 1 / 16 := by norm_num
  obtain ⟨epsCert, rho₀, hcertificate⟩ :=
    exists_lemma49RelativeGreendlingerCell_of_relativeGreendlinger
      hgeom D hemb (1 / 1000) hmuCertPos hmuCertUpper
  obtain ⟨K, hshadow⟩ :=
    exists_lemma49ContiguityShadow_constant delta epsCert
  let b := 8 * delta + 2
  let eps := max epsCert (2 * K)
  let scale := 1000 * (4 * b + 24 * K + 18 * epsCert + 18)
  let rho := max rho₀ scale
  have hepsCert : epsCert ≤ eps := Nat.le_max_left _ _
  have hconnectors : 2 * K ≤ eps := Nat.le_max_right _ _
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : scale ≤ rho := Nat.le_max_right _ _
  refine ⟨eps, rho, delta, hdelta, ?_⟩
  intro W v hv hinput g n hshort Z hlongPeriod
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  letI : N.Normal := Subgroup.normalClosure_normal
  have hfinalSym : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 100000) rho := hinput.restrict_symmetrized hv
  have hmuMono : (1 / 100000 : ℝ) ≤ 1 / 1000 := by norm_num
  have hcertInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho :=
    hfinalSym.mono_parameters hepsCert hmuMono le_rfl
  obtain ⟨C⟩ := hcertificate rho hrho₀ v g n hcertInput Z
  obtain ⟨Sh⟩ := hshadow G inferInstance Lambda D v g n rho Z C N
    inferInstance hdelta hcertInput hshort hlongPeriod
  apply false_of_longPeriod_powerDiagram_of_cell D Z C Sh hdelta hshort
    hcertInput hfinalSym
  · simpa only [b, scale] using hrhoScale
  · exact hconnectors
  · exact hlongPeriod

/-! ## Model check -/

/-- The long-period branch is empty in the trivial group because no
nontrivial power diagram exists. -/
theorem no_longPeriod_powerDiagram_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (v : List (GGT.RelLetter PUnit Lambda)) (n delta : ℕ) :
    ∀ Z : Lemma49GeodesicPowerDiagram D v 1 n,
      8 * delta + 2 ≤ Z.boundaryWord.length → False := by
  intro Z _
  exact Z.power_ne_one (Subsingleton.elim _ _)

end HullSC
end GroupApproximation
