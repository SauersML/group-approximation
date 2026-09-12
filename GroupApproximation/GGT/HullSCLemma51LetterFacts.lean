import GroupApproximation.GGT.HullSCLemma44RelativeDehnRotation
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity facts for the Lemma 5.1 letter pullback

The letter pullback cuts a quotient-null word along the certificate cell of Osin's Lemma 4.4.
Its bookkeeping uses four facts that main already implies but does not state.

* `RelativeBoundaryContiguity.exterior_length_div_four_le_wordNorm_boundaryArc`: the removed
  boundary arc spells an element of relative norm at least `|exterior| / 4 - 1 - |sides|`.
  This is `(4,1)` quasi-geodesicity of the relator prefix together with `exterior_value`.
* `exists_long_cut_of_certificate`: at `mu ≤ 1/1000` and `20 (eps + 1) ≤ rho`, the certificate
  cell gives a strictly shorter replacement AND `2 eps + 1 < |arc|`.  The second clause
  refutes a shortcut `leftSide · (one peripheral letter) · rightSide` between the arc's ends.
* `RelativeBoundaryContiguity.exists_geodesicSides`: both sides re-spell as relative geodesic
  words with the same values.  Nothing else changes, since `exterior_value` reads the sides
  only through their values.
* `exists_relArc_of_rotate_decomposition`: a block of the rotated value word is the image of a
  block of the rotated relative spelling, so an arc of the certificate is an arc of the
  relative word.

The rotation and conjugation API for cyclic cuts is `HullSCLemma44RelativeDehnRotation`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

namespace RelativeBoundaryContiguity

/-- **The removed arc is at least a quarter of the exterior, less the two sides.** -/
theorem exterior_length_div_four_le_wordNorm_boundaryArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hqg : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      (fun i => GGT.RelLetter.listVal (relator.take i)) relator.length) :
    (C.exterior.length : ℝ) / 4 - 1 - C.leftSide.length - C.rightSide.length ≤
      (wordNorm D.alphabet.carrier C.boundaryArc.prod : ℝ) := by
  have hexteriorLe : C.exterior.length ≤ relator.length := C.exterior_length_le_relator
  have htake : relator.take C.exterior.length = C.exterior := by
    calc
      relator.take C.exterior.length =
          (C.exterior ++ C.remainder).take C.exterior.length :=
        congrArg (List.take C.exterior.length) C.relator_decomposition
      _ = C.exterior := by simp only [List.take_left]
  have hlowerRaw := (hqg 0 C.exterior.length (Nat.zero_le _) hexteriorLe).1
  have hzero : GGT.RelLetter.listVal (relator.take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm D.alphabet.carrier (GGT.RelLetter.listVal C.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hleftRel : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal C.leftSide) ≤
      C.leftSide.length :=
    wordNorm_listVal_le_length D C.leftSide C.leftSide_admissible
  have hrightRel : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal C.rightSide) ≤
      C.rightSide.length :=
    wordNorm_listVal_le_length D C.rightSide C.rightSide_admissible
  have hmulOne := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide) C.boundaryArc.prod
  have hmulTwo := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide * C.boundaryArc.prod)
    (GGT.RelLetter.listVal C.rightSide)
  have hupperNat : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal C.exterior) ≤
      C.leftSide.length + wordNorm D.alphabet.carrier C.boundaryArc.prod +
        C.rightSide.length := by
    rw [C.exterior_value]
    omega
  have hupperReal :
      (wordNorm D.alphabet.carrier (GGT.RelLetter.listVal C.exterior) : ℝ) ≤
        (C.leftSide.length : ℝ) + (wordNorm D.alphabet.carrier C.boundaryArc.prod : ℝ) +
          C.rightSide.length := by
    exact_mod_cast hupperNat
  linarith

end RelativeBoundaryContiguity

/-- **The certificate cut at `20 (eps + 1) ≤ rho`, with a long arc.**  The certificate cell
gives a strictly shorter replacement, and the removed arc spells an element of relative norm
greater than `2 eps + 1`. -/
theorem exists_long_cut_of_certificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z) :
    ∃ (i : Fin Z.cells.length)
      (C : RelativeBoundaryContiguity D eps K.boundaryWord (K.cellLabel i)),
      K.contiguity i = some C ∧
        C.replacementWord.length < C.boundaryArc.length ∧
          2 * eps + 1 < wordNorm D.alphabet.carrier C.boundaryArc.prod := by
  obtain ⟨i, C, hcontiguity, hlarge⟩ := K.largeCell
  have hrelatorMem : K.cellLabel i ∈ W := K.cellLabel_mem i
  have hlongNat : rho ≤ (K.cellLabel i).length := hsc.long (K.cellLabel i) hrelatorMem
  have hlengthNat : (K.cellLabel i).length = C.exterior.length + C.remainder.length := by
    have hlength := congrArg List.length C.relator_decomposition
    simpa only [List.length_append] using hlength
  have hlengthReal : ((K.cellLabel i).length : ℝ) =
      (C.exterior.length : ℝ) + (C.remainder.length : ℝ) := by
    exact_mod_cast hlengthNat
  have hrelatorNonneg : (0 : ℝ) ≤ (K.cellLabel i).length := by positivity
  have hcoeff : (977 / 1000 : ℝ) ≤ 1 - 23 * mu := by linarith
  have hexteriorLower : (977 / 1000 : ℝ) * (K.cellLabel i).length ≤ C.exterior.length :=
    le_trans (mul_le_mul_of_nonneg_right hcoeff hrelatorNonneg) hlarge
  have hremainderUpper :
      (C.remainder.length : ℝ) ≤ (23 / 1000 : ℝ) * (K.cellLabel i).length := by
    linarith
  have harc := C.exterior_length_div_four_le_wordNorm_boundaryArc
    (hsc.quasiGeodesic (K.cellLabel i) hrelatorMem)
  have harcWord : IsWord D.alphabet.carrier C.boundaryArc C.boundaryArc.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    have hboundaryWord : IsWord D.alphabet.carrier K.boundaryWord Z.boundary := by
      rw [K.boundaryWord_eq]
      exact Z.boundaryWord_isWord
    exact hboundaryWord.letters x (C.boundaryArc_mem_boundaryWord hx)
  have harcRel : wordNorm D.alphabet.carrier C.boundaryArc.prod ≤ C.boundaryArc.length :=
    wordNorm_le_length harcWord
  have harcRelReal :
      (wordNorm D.alphabet.carrier C.boundaryArc.prod : ℝ) ≤ C.boundaryArc.length := by
    exact_mod_cast harcRel
  have hleftShort : (C.leftSide.length : ℝ) ≤ eps := by exact_mod_cast C.leftSide_short
  have hrightShort : (C.rightSide.length : ℝ) ≤ eps := by exact_mod_cast C.rightSide_short
  have hlongReal : (20 : ℝ) * ((eps : ℝ) + 1) ≤ (K.cellLabel i).length := by
    have hcombined : 20 * (eps + 1) ≤ (K.cellLabel i).length := le_trans hrho hlongNat
    exact_mod_cast hcombined
  have hreplacementLength : (C.replacementWord.length : ℝ) =
      C.leftSide.length + C.remainder.length + C.rightSide.length := by
    exact_mod_cast C.replacementWord_length
  refine ⟨i, C, hcontiguity, ?_, ?_⟩
  · have hstrict : (C.replacementWord.length : ℝ) < C.boundaryArc.length := by
      linarith [(Nat.cast_nonneg eps : (0 : ℝ) ≤ eps)]
    exact_mod_cast hstrict
  · have hlong : ((2 * eps + 1 : ℕ) : ℝ) <
        (wordNorm D.alphabet.carrier C.boundaryArc.prod : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg eps : (0 : ℝ) ≤ eps)]
    exact_mod_cast hlong

namespace RelativeBoundaryContiguity

/-- **The two sides re-spell as relative geodesic words.**  The relator split, the rotation
and the boundary arc stay the same, and each new side is a geodesic word for its old value, so
it has at most one peripheral letter in each coset. -/
theorem exists_geodesicSides
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    ∃ C' : RelativeBoundaryContiguity D eps boundaryWord relator,
      C'.exterior = C.exterior ∧ C'.remainder = C.remainder ∧
        C'.rotation = C.rotation ∧ C'.boundaryBefore = C.boundaryBefore ∧
          C'.boundaryArc = C.boundaryArc ∧ C'.boundaryAfter = C.boundaryAfter ∧
            GGT.OsinComponents.IsGeodesicWord D 1
              (GGT.RelLetter.listVal C.leftSide) C'.leftSide ∧
            GGT.OsinComponents.IsGeodesicWord D 1
              (GGT.RelLetter.listVal C.rightSide) C'.rightSide := by
  obtain ⟨wl, hwl⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 (GGT.RelLetter.listVal C.leftSide)
  obtain ⟨wr, hwr⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 (GGT.RelLetter.listVal C.rightSide)
  have hvall : GGT.RelLetter.listVal wl = GGT.RelLetter.listVal C.leftSide := by
    simpa only [one_mul] using hwl.2.1
  have hvalr : GGT.RelLetter.listVal wr = GGT.RelLetter.listVal C.rightSide := by
    simpa only [one_mul] using hwr.2.1
  have hlenl : wl.length ≤ eps := by
    rw [hwl.2.2, wordDist_one_left]
    exact le_trans (wordNorm_listVal_le_length D C.leftSide C.leftSide_admissible)
      C.leftSide_short
  have hlenr : wr.length ≤ eps := by
    rw [hwr.2.2, wordDist_one_left]
    exact le_trans (wordNorm_listVal_le_length D C.rightSide C.rightSide_admissible)
      C.rightSide_short
  have hext : GGT.RelLetter.listVal C.exterior =
      GGT.RelLetter.listVal wl * C.boundaryArc.prod * GGT.RelLetter.listVal wr := by
    rw [hvall, hvalr]
    exact C.exterior_value
  refine ⟨{ C with
    leftSide := wl
    rightSide := wr
    leftSide_admissible := hwl.1
    rightSide_admissible := hwr.1
    leftSide_short := hlenl
    rightSide_short := hlenr
    exterior_value := hext }, rfl, rfl, rfl, rfl, rfl, rfl, hwl, hwr⟩

end RelativeBoundaryContiguity

/-- **A block of the rotated value word is the image of a block of the rotated relative
spelling.** -/
theorem exists_relArc_of_rotate_decomposition
    {G : Type u} {Lambda : Type w}
    {outer : List (GGT.RelLetter G Lambda)} {boundaryWord before arc after : List G}
    {r : ℕ} (hmap : outer.map GGT.RelLetter.val = boundaryWord)
    (hdec : boundaryWord.rotate r = before ++ arc ++ after) :
    ∃ before' arc' after' : List (GGT.RelLetter G Lambda),
      outer.rotate r = before' ++ arc' ++ after' ∧
        before'.map GGT.RelLetter.val = before ∧ arc'.map GGT.RelLetter.val = arc ∧
          after'.map GGT.RelLetter.val = after := by
  have hrot : (outer.rotate r).map GGT.RelLetter.val = before ++ arc ++ after := by
    rw [List.map_rotate, hmap, hdec]
  obtain ⟨l₁, after', hsplit, h₁, hafter⟩ := List.map_eq_append_iff.mp hrot
  obtain ⟨before', arc', hsplit', hbefore, harc⟩ := List.map_eq_append_iff.mp h₁
  exact ⟨before', arc', after', by rw [hsplit, hsplit'], hbefore, harc, hafter⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.RelativeBoundaryContiguity.exterior_length_div_four_le_wordNorm_boundaryArc
#audit_axioms GroupApproximation.HullSC.exists_long_cut_of_certificate
#audit_axioms GroupApproximation.HullSC.RelativeBoundaryContiguity.exists_geodesicSides
#audit_axioms GroupApproximation.HullSC.exists_relArc_of_rotate_decomposition
