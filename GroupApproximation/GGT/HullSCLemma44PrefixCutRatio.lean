import GroupApproximation.GGT.HullSCLemma44PrefixCut

/-!
# Quantitative prefix cuts for Hull's Lemma 4.4

Osin's proof of Lemma 5.1 charges the prefix-triangle filling of a selected
relator cell to the exterior arc removed from the current boundary.  A merely
strict shortening does not give that charge.  This file derives the two
uniform estimates needed by the weighted induction from the
`1 - 23 * mu` Greendlinger coefficient:

* twice the replacement length is at most the removed boundary-arc length;
* the relator length is at most five times that boundary-arc length.

The numerical hypotheses `mu <= 1/1000` and
`100 * (eps + 1) <= rho` are stronger than the short-word threshold and may be
imposed when `rho` is chosen.  The last theorem adds the prefix-quotient norm
bound from `HullSCLemma44PrefixCut`, producing all three estimates from one
certificate-selected cell.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

namespace RelativeBoundaryContiguity

/-! ## Elementary consequences of the ratio bounds -/

/-- A positive relator bounded by five times an exterior boundary arc forces
that arc to be nonempty. -/
theorem boundaryArc_length_pos_of_relator_length_le_five
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelator : 0 < relator.length)
    (hbound : relator.length ≤ 5 * C.boundaryArc.length) :
    0 < C.boundaryArc.length := by
  omega

/-- The factor-two estimate, together with a nonempty removed arc, implies
the strict shortening required by the ordinary Dehn cut. -/
theorem replacementWord_length_lt_boundaryArc_of_twice_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hpositive : 0 < C.boundaryArc.length)
    (hratio : 2 * C.replacementWord.length ≤ C.boundaryArc.length) :
    C.replacementWord.length < C.boundaryArc.length := by
  omega

/-! ## Estimates for the cell selected by a certificate -/

/-- The Greendlinger cell selected at the stronger length threshold has a
replacement whose doubled length is bounded by the removed arc, and its full
relator is at most five times the removed arc. -/
theorem exists_ratio_bounded_cut_of_certificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 100 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z) :
    ∃ (i : Fin Z.cells.length)
      (C : RelativeBoundaryContiguity D eps K.boundaryWord (K.cellLabel i)),
      K.contiguity i = some C ∧
        2 * C.replacementWord.length ≤ C.boundaryArc.length ∧
          (K.cellLabel i).length ≤ 5 * C.boundaryArc.length ∧
            0 < C.boundaryArc.length := by
  obtain ⟨i, C, hcontiguity, hlarge⟩ := K.largeCell
  have hrelatorMem : K.cellLabel i ∈ W := K.cellLabel_mem i
  have hlongNat : rho ≤ (K.cellLabel i).length :=
    hsc.long (K.cellLabel i) hrelatorMem
  have hlengthNat : (K.cellLabel i).length =
      C.exterior.length + C.remainder.length := by
    have hlength := congrArg List.length C.relator_decomposition
    simpa only [List.length_append] using hlength
  have hlengthReal : ((K.cellLabel i).length : ℝ) =
      (C.exterior.length : ℝ) + (C.remainder.length : ℝ) := by
    exact_mod_cast hlengthNat
  have hrelatorNonneg : (0 : ℝ) ≤ (K.cellLabel i).length := by
    positivity
  have hcoeff : (977 / 1000 : ℝ) ≤ 1 - 23 * mu := by
    linarith
  have hexteriorLower : (977 / 1000 : ℝ) * (K.cellLabel i).length ≤
      C.exterior.length := by
    exact le_trans (mul_le_mul_of_nonneg_right hcoeff hrelatorNonneg) hlarge
  have hremainderUpper : (C.remainder.length : ℝ) ≤
      (23 / 1000 : ℝ) * (K.cellLabel i).length := by
    linarith
  have hexteriorLe : C.exterior.length ≤ (K.cellLabel i).length :=
    C.exterior_length_le_relator
  have htake : (K.cellLabel i).take C.exterior.length = C.exterior := by
    calc
      (K.cellLabel i).take C.exterior.length =
          (C.exterior ++ C.remainder).take C.exterior.length :=
        congrArg (List.take C.exterior.length) C.relator_decomposition
      _ = C.exterior := by simp only [List.take_left]
  have hqg := hsc.quasiGeodesic (K.cellLabel i) hrelatorMem
  have hlowerRaw := (hqg 0 C.exterior.length (Nat.zero_le _)
    hexteriorLe).1
  have hzero : GGT.RelLetter.listVal ((K.cellLabel i).take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hleftRel : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.leftSide) ≤ C.leftSide.length :=
    wordNorm_listVal_le_length D C.leftSide C.leftSide_admissible
  have hrightRel : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide) ≤ C.rightSide.length :=
    wordNorm_listVal_le_length D C.rightSide C.rightSide_admissible
  have harcWord : IsWord D.alphabet.carrier
      C.boundaryArc C.boundaryArc.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    have hboundaryWord : IsWord D.alphabet.carrier
        K.boundaryWord Z.boundary := by
      rw [K.boundaryWord_eq]
      exact Z.boundaryWord_isWord
    exact hboundaryWord.letters x (C.boundaryArc_mem_boundaryWord hx)
  have harcRel : wordNorm D.alphabet.carrier C.boundaryArc.prod ≤
      C.boundaryArc.length := wordNorm_le_length harcWord
  have hmulOne := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide) C.boundaryArc.prod
  have hmulTwo := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide * C.boundaryArc.prod)
    (GGT.RelLetter.listVal C.rightSide)
  have hupperNat : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.exterior) ≤
        C.leftSide.length + C.boundaryArc.length + C.rightSide.length := by
    rw [C.exterior_value]
    omega
  have hupperReal : (wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.exterior) : ℝ) ≤
        (C.leftSide.length : ℝ) + C.boundaryArc.length +
          C.rightSide.length := by
    exact_mod_cast hupperNat
  have hleftShort : (C.leftSide.length : ℝ) ≤ eps := by
    exact_mod_cast C.leftSide_short
  have hrightShort : (C.rightSide.length : ℝ) ≤ eps := by
    exact_mod_cast C.rightSide_short
  have hlongReal : (100 : ℝ) * ((eps : ℝ) + 1) ≤
      (K.cellLabel i).length := by
    have hcombined : 100 * (eps + 1) ≤ (K.cellLabel i).length :=
      le_trans hrho hlongNat
    exact_mod_cast hcombined
  have hreplacementLength : (C.replacementWord.length : ℝ) =
      C.leftSide.length + C.remainder.length + C.rightSide.length := by
    exact_mod_cast C.replacementWord_length
  have hratioReal : (2 * C.replacementWord.length : ℕ) ≤
      C.boundaryArc.length := by
    exact_mod_cast (show (2 : ℝ) * C.replacementWord.length ≤
      C.boundaryArc.length by nlinarith)
  have hrelatorReal : (K.cellLabel i).length ≤
      (5 : ℝ) * C.boundaryArc.length := by
    nlinarith
  have hrelatorNat : (K.cellLabel i).length ≤
      5 * C.boundaryArc.length := by
    exact_mod_cast hrelatorReal
  have hrelatorPos : 0 < (K.cellLabel i).length := by
    have hrhoPos : 0 < rho := by omega
    omega
  have harcPos : 0 < C.boundaryArc.length :=
    C.boundaryArc_length_pos_of_relator_length_le_five
      hrelatorPos hrelatorNat
  exact ⟨i, C, hcontiguity, hratioReal, hrelatorNat, harcPos⟩

/-! ## Quotient form -/

/-- One selected cell simultaneously supplies the ratio bounds and the
uniform prefix-quotient shortcut. -/
theorem exists_ratio_bounded_prefixQuotient_cut_of_certificate
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 100 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    ∃ (i : Fin Z.cells.length)
      (C : RelativeBoundaryContiguity D eps K.boundaryWord (K.cellLabel i)),
      K.contiguity i = some C ∧
        2 * C.replacementWord.length ≤ C.boundaryArc.length ∧
          (K.cellLabel i).length ≤ 5 * C.boundaryArc.length ∧
            0 < C.boundaryArc.length ∧
              wordNorm
                (D.prefixQuotient W hsc.toIsSmallCancellation q hq).alphabet.carrier
                (q C.boundaryArc.prod) ≤ 2 * eps + 1 := by
  obtain ⟨i, C, hcontiguity, hratio, hrelator, harcPos⟩ :=
    exists_ratio_bounded_cut_of_certificate D hsc hmu hrho K
  have hkill : q (GGT.RelLetter.listVal (K.cellLabel i)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure
      ⟨K.cellLabel i, K.cellLabel_mem i, rfl⟩
  refine ⟨i, C, hcontiguity, hratio, hrelator, harcPos, ?_⟩
  exact C.wordNorm_map_boundaryArc_prefixQuotient_le
    hsc.toIsSmallCancellation (K.cellLabel_mem i) q hq hkill

end RelativeBoundaryContiguity
end HullSC
end GroupApproximation
