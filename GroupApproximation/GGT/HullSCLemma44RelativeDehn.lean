import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement

/-!
# The relative Dehn shortening step in Hull's Lemma 4.4

Osin's proof of Theorem 4.1, equations (18)--(21), cuts a relator cell along
the contiguity region supplied by Lemma 4.4.  The boundary arc is replaced by
the inverse of the complementary relator arc, with the inverses of the two
short connector words on its sides.  The old and new words have the same
image in the quotient.

This file proves that cut using the finite certificate interface.  If
`mu <= 1/1000` and `rho >= 20 * (eps + 1)`, the replacement is strictly
shorter.  The proof combines the `1 - 23 * mu` exterior proportion with the
`(4,1)` quasi-geodesic lower bound on the exterior prefix.  It does not use
the combinatorial-map implementation of the contiguity region.

The result is the one-cell induction step needed by the relative linear-area
argument.  Hyperbolicity of the quotient Cayley graph additionally needs the
source relative filling comparison used in Osin's Lemma 5.1.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

namespace RelativeBoundaryContiguity

/-- The value of a legal relative letter belongs to the full relative
alphabet. -/
theorem val_mem_alphabet_of_isLetter
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {a : GGT.RelLetter G Lambda}
    (ha : D.IsLetter a) : a.val ∈ D.alphabet.carrier := by
  cases a with
  | base x => exact Set.mem_union_left _ ha
  | comp lam x =>
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, ha⟩)

/-- An admissible relative word gives an ordinary word of the same length in
the full relative alphabet. -/
theorem wordNorm_listVal_le_length
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (word : List (GGT.RelLetter G Lambda))
    (hword : RelWord.IsAdmissible D word) :
    wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word) ≤ word.length := by
  have hisWord : IsWord D.alphabet.carrier
      (word.map GGT.RelLetter.val) (GGT.RelLetter.listVal word) := by
    refine ⟨?_, rfl⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact val_mem_alphabet_of_isLetter D (hword a ha)
  have hlength := wordNorm_le_length hisWord
  rwa [List.length_map] at hlength

/-- The word replacing the outer boundary arc: inverse left connector,
inverse complementary relator arc, and inverse right connector. -/
def replacementWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) : List G :=
  (RelWord.revInv C.leftSide).map GGT.RelLetter.val ++
    (RelWord.revInv C.remainder).map GGT.RelLetter.val ++
      (RelWord.revInv C.rightSide).map GGT.RelLetter.val

/-- Replace the selected outer arc while retaining its prefix and suffix. -/
def shortenedBoundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) : List G :=
  C.boundaryBefore ++ C.replacementWord ++ C.boundaryAfter

/-- The replacement spells the product of the three inverse path values. -/
theorem replacementWord_prod
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    C.replacementWord.prod =
      (GGT.RelLetter.listVal C.leftSide)⁻¹ *
        (GGT.RelLetter.listVal C.remainder)⁻¹ *
          (GGT.RelLetter.listVal C.rightSide)⁻¹ := by
  rw [replacementWord, List.prod_append, List.prod_append]
  change GGT.RelLetter.listVal (RelWord.revInv C.leftSide) *
      GGT.RelLetter.listVal (RelWord.revInv C.remainder) *
        GGT.RelLetter.listVal (RelWord.revInv C.rightSide) = _
  rw [RelWord.listVal_revInv, RelWord.listVal_revInv,
    RelWord.listVal_revInv]

/-- The replacement and selected boundary arc have equal quotient values
when the cell relator is killed. -/
theorem map_replacementWord_prod_eq_boundaryArc_prod
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hrelator : q (GGT.RelLetter.listVal relator) = 1) :
    q C.replacementWord.prod = q C.boundaryArc.prod := by
  have hrelatorValue : GGT.RelLetter.listVal relator =
      GGT.RelLetter.listVal C.exterior *
        GGT.RelLetter.listVal C.remainder := by
    calc
      GGT.RelLetter.listVal relator =
          GGT.RelLetter.listVal (C.exterior ++ C.remainder) :=
        congrArg GGT.RelLetter.listVal C.relator_decomposition
      _ = GGT.RelLetter.listVal C.exterior *
          GGT.RelLetter.listVal C.remainder := by
        rw [RelWord.listVal_append]
  rw [hrelatorValue, C.exterior_value, map_mul, map_mul, map_mul] at hrelator
  apply_fun (fun x : Q =>
    (q (GGT.RelLetter.listVal C.leftSide))⁻¹ * x *
      (q (GGT.RelLetter.listVal C.remainder))⁻¹ *
        (q (GGT.RelLetter.listVal C.rightSide))⁻¹) at hrelator
  rw [C.replacementWord_prod, map_mul, map_mul, map_inv, map_inv,
    map_inv]
  group at hrelator ⊢
  exact hrelator.symm

/-- Performing the cut preserves the element represented in the quotient. -/
theorem map_shortenedBoundaryWord_prod_eq
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (q : G →* Q) (hrelator : q (GGT.RelLetter.listVal relator) = 1)
    (hrot : C.rotation = 0) :
    q C.shortenedBoundaryWord.prod = q boundaryWord.prod := by
  have harc := C.map_replacementWord_prod_eq_boundaryArc_prod q hrelator
  have hshortenedValue : C.shortenedBoundaryWord.prod =
      C.boundaryBefore.prod * C.replacementWord.prod *
        C.boundaryAfter.prod := by
    rw [shortenedBoundaryWord, List.prod_append, List.prod_append]
  have hboundaryValue : boundaryWord.prod =
      C.boundaryBefore.prod * C.boundaryArc.prod *
        C.boundaryAfter.prod := by
    calc
      boundaryWord.prod =
          (C.boundaryBefore ++ C.boundaryArc ++ C.boundaryAfter).prod :=
        congrArg List.prod (C.boundary_decomposition_of_rotation_zero hrot)
      _ = C.boundaryBefore.prod * C.boundaryArc.prod *
          C.boundaryAfter.prod := by
        rw [List.prod_append, List.prod_append]
  rw [hshortenedValue, hboundaryValue, map_mul, map_mul, map_mul, map_mul,
    harc]

/-- One cut removes exactly one conjugate of the selected relator value from
the source boundary.  This is the algebraic area step in Osin Lemma 5.1. -/
theorem boundaryWord_prod_eq_conjugate_relator_mul_shortened
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrot : C.rotation = 0) :
    boundaryWord.prod =
      (C.boundaryBefore.prod *
          (GGT.RelLetter.listVal C.leftSide)⁻¹) *
        GGT.RelLetter.listVal relator *
        (C.boundaryBefore.prod *
            (GGT.RelLetter.listVal C.leftSide)⁻¹)⁻¹ *
        C.shortenedBoundaryWord.prod := by
  have hrelatorValue : GGT.RelLetter.listVal relator =
      GGT.RelLetter.listVal C.exterior *
        GGT.RelLetter.listVal C.remainder := by
    calc
      GGT.RelLetter.listVal relator =
          GGT.RelLetter.listVal (C.exterior ++ C.remainder) :=
        congrArg GGT.RelLetter.listVal C.relator_decomposition
      _ = GGT.RelLetter.listVal C.exterior *
          GGT.RelLetter.listVal C.remainder := by
        rw [RelWord.listVal_append]
  have hboundaryValue : boundaryWord.prod =
      C.boundaryBefore.prod * C.boundaryArc.prod *
        C.boundaryAfter.prod := by
    calc
      boundaryWord.prod =
          (C.boundaryBefore ++ C.boundaryArc ++ C.boundaryAfter).prod :=
        congrArg List.prod (C.boundary_decomposition_of_rotation_zero hrot)
      _ = C.boundaryBefore.prod * C.boundaryArc.prod *
          C.boundaryAfter.prod := by
        rw [List.prod_append, List.prod_append]
  have hshortenedValue : C.shortenedBoundaryWord.prod =
      C.boundaryBefore.prod * C.replacementWord.prod *
        C.boundaryAfter.prod := by
    rw [shortenedBoundaryWord, List.prod_append, List.prod_append]
  rw [hboundaryValue, hshortenedValue, C.replacementWord_prod,
    hrelatorValue, C.exterior_value]
  group

/-- Formal inversion preserves length. -/
theorem length_revInv
    {G : Type u} [Group G] {Lambda : Type w}
    (word : List (GGT.RelLetter G Lambda)) :
    (RelWord.revInv word).length = word.length := by
  rw [RelWord.revInv, List.length_reverse, List.length_map]

/-- Length of the three-piece replacement. -/
theorem replacementWord_length
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    C.replacementWord.length =
      C.leftSide.length + C.remainder.length + C.rightSide.length := by
  simp only [replacementWord, List.length_append, List.length_map,
    length_revInv]

/-- Length of the cut boundary word. -/
theorem shortenedBoundaryWord_length
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    C.shortenedBoundaryWord.length =
      C.boundaryBefore.length + C.replacementWord.length +
        C.boundaryAfter.length := by
  simp only [shortenedBoundaryWord, List.length_append]

/-- A shorter replacement arc makes the entire cut boundary shorter. -/
theorem shortenedBoundaryWord_length_lt
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hshort : C.replacementWord.length < C.boundaryArc.length) :
    C.shortenedBoundaryWord.length < boundaryWord.length := by
  have hboundaryLength := congrArg List.length C.boundary_decomposition
  rw [C.shortenedBoundaryWord_length]
  simp only [List.length_append, List.length_rotate] at hboundaryLength
  omega

/-- Values of formally inverted admissible letters remain in the full
relative alphabet, even when a base inverse is represented peripherally. -/
theorem val_mem_alphabet_of_mem_revInv
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : RelWord.IsAdmissible D word)
    {a : GGT.RelLetter G Lambda} (ha : a ∈ RelWord.revInv word) :
    a.val ∈ D.alphabet.carrier := by
  have hainv : RelWord.inv a ∈ word := RelWord.inv_mem_of_mem_revInv ha
  have hinvLetter : D.IsLetter (RelWord.inv a) := hword _ hainv
  have hinvValue : (RelWord.inv a).val ∈ D.alphabet.carrier :=
    val_mem_alphabet_of_isLetter D hinvLetter
  have hclosed := D.alphabet.symmetricGenerating.inv_mem _ hinvValue
  rw [RelWord.val_inv, inv_inv] at hclosed
  exact hclosed

/-- The replacement is a word on the full source relative alphabet. -/
theorem replacementWord_isWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator) :
    IsWord D.alphabet.carrier C.replacementWord C.replacementWord.prod := by
  have hremainder : RelWord.IsAdmissible D C.remainder := by
    intro a ha
    apply hrelatorAdmissible a
    rw [C.relator_decomposition]
    exact List.mem_append_right C.exterior ha
  refine ⟨?_, rfl⟩
  intro x hx
  simp only [replacementWord, List.mem_append, List.mem_map] at hx
  rcases hx with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
  · exact val_mem_alphabet_of_mem_revInv D C.leftSide_admissible ha
  · exact val_mem_alphabet_of_mem_revInv D hremainder ha
  · exact val_mem_alphabet_of_mem_revInv D C.rightSide_admissible ha

/-- The cut word remains on the full relative alphabet. -/
theorem shortenedBoundaryWord_isWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator)
    (hboundary : IsWord D.alphabet.carrier boundaryWord boundaryWord.prod)
    (hrelatorAdmissible : RelWord.IsAdmissible D relator) :
    IsWord D.alphabet.carrier C.shortenedBoundaryWord
      C.shortenedBoundaryWord.prod := by
  have hreplacement := C.replacementWord_isWord hrelatorAdmissible
  refine ⟨?_, rfl⟩
  intro x hx
  simp only [shortenedBoundaryWord, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · apply hboundary.letters x
    apply (List.mem_rotate (n := C.rotation)).mp
    rw [C.boundary_decomposition]
    exact List.mem_append_left C.boundaryAfter
      (List.mem_append_left C.boundaryArc hx)
  · exact hreplacement.letters x hx
  · apply hboundary.letters x
    apply (List.mem_rotate (n := C.rotation)).mp
    rw [C.boundary_decomposition]
    exact List.mem_append_right (C.boundaryBefore ++ C.boundaryArc) hx

end RelativeBoundaryContiguity

/-! ## Quantitative shortening -/

/-- The certificate's exterior cell gives a strictly shorter quotient word.
This is the cut used in the boundary-length induction of Osin Lemma 5.1. -/
theorem replacementWord_length_lt_boundaryArc_of_certificate
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
        C.replacementWord.length < C.boundaryArc.length := by
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
  have hrelatorNonneg : (0 : ℝ) ≤ (K.cellLabel i).length := by positivity
  have hcoeff : (977 / 1000 : ℝ) ≤ 1 - 23 * mu := by linarith
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
    RelativeBoundaryContiguity.wordNorm_listVal_le_length D C.leftSide
      C.leftSide_admissible
  have hrightRel : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide) ≤ C.rightSide.length :=
    RelativeBoundaryContiguity.wordNorm_listVal_le_length D C.rightSide
      C.rightSide_admissible
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
  have hlongReal : (20 : ℝ) * ((eps : ℝ) + 1) ≤
      (K.cellLabel i).length := by
    have hcombined : 20 * (eps + 1) ≤ (K.cellLabel i).length :=
      le_trans hrho hlongNat
    exact_mod_cast hcombined
  have hreplacementLength : (C.replacementWord.length : ℝ) =
      C.leftSide.length + C.remainder.length + C.rightSide.length := by
    exact_mod_cast C.replacementWord_length
  have hstrict : (C.replacementWord.length : ℝ) <
      C.boundaryArc.length := by
    nlinarith
  exact ⟨i, C, hcontiguity, by exact_mod_cast hstrict⟩

/-! ## Packaged induction step -/

/-- A one-relator local cut with the same quotient boundary value.  Retaining
the relator and its contiguity data prevents the shortening premise from
collapsing to an arbitrary choice of a shorter null word. -/
structure RelativeDehnCut
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (eps : ℕ)
    (q : G →* Q) (boundaryWord : List G) where
  relator : List (GGT.RelLetter G Lambda)
  relator_mem : relator ∈ W
  contiguity : RelativeBoundaryContiguity D eps boundaryWord relator
  shortenedWord_isWord : IsWord D.alphabet.carrier
    contiguity.shortenedBoundaryWord contiguity.shortenedBoundaryWord.prod
  quotient_value : q contiguity.shortenedBoundaryWord.prod = q boundaryWord.prod
  replacement_length_lt :
    contiguity.replacementWord.length < contiguity.boundaryArc.length

namespace RelativeDehnCut

/-- Strict shortening of the local arc strictly shortens the whole word. -/
theorem length_lt
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps : ℕ}
    {q : G →* Q} {boundaryWord : List G}
    (C : RelativeDehnCut D W eps q boundaryWord) :
    C.contiguity.shortenedBoundaryWord.length < boundaryWord.length :=
  C.contiguity.shortenedBoundaryWord_length_lt C.replacement_length_lt

end RelativeDehnCut

/-- Every certificate supplies the strict one-cell cut used by Osin's
boundary-length induction, provided the quotient kills every relator.

**`hrot` is a residue of the boundary-cycle rotation carried by
`RelativeBoundaryContiguity` (see its docstring).**  The value-level identity
this theorem needs only holds at the wrap-free cut; every certificate
currently produced by `RelativeDiagramCertificate.largeCell` fixes the
default `rotation := 0`, so `hrot` is discharged by `rfl` at every present
call site.  A future certificate builder that actually wraps the cut will
need to supply a genuine proof here (or this theorem will need the explicit
conjugation correction instead). -/
theorem exists_relativeDehnCut_of_certificate
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hkill : ∀ relator ∈ W, q (GGT.RelLetter.listVal relator) = 1)
    (hrot : ∀ {i : Fin Z.cells.length}
      {C : RelativeBoundaryContiguity D eps K.boundaryWord (K.cellLabel i)},
      K.contiguity i = some C → C.rotation = 0) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) := by
  obtain ⟨i, C, hcontiguity, hshort⟩ :=
    replacementWord_length_lt_boundaryArc_of_certificate D hsc hmu hrho K
  have hboundary : IsWord D.alphabet.carrier K.boundaryWord
      K.boundaryWord.prod := by
    refine ⟨?_, ?_⟩
    · intro x hx
      apply Z.boundaryWord_isWord.letters x
      rwa [← K.boundaryWord_eq]
    · exact rfl
  have hrelatorAdmissible : RelWord.IsAdmissible D (K.cellLabel i) :=
    hsc.admissible (K.cellLabel i) (K.cellLabel_mem i)
  refine ⟨{
    relator := K.cellLabel i
    relator_mem := K.cellLabel_mem i
    contiguity := C
    shortenedWord_isWord := C.shortenedBoundaryWord_isWord hboundary
      hrelatorAdmissible
    quotient_value := C.map_shortenedBoundaryWord_prod_eq q
      (hkill (K.cellLabel i) (K.cellLabel_mem i)) (hrot hcontiguity)
    replacement_length_lt := hshort }⟩

/-- The normal-closure kernel equation supplies the relator-killing premise
of the packaged cut.  See `exists_relativeDehnCut_of_certificate` for `hrot`. -/
theorem exists_relativeDehnCut_of_kernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hrot : ∀ {i : Fin Z.cells.length}
      {C : RelativeBoundaryContiguity D eps K.boundaryWord (K.cellLabel i)},
      K.contiguity i = some C → C.rotation = 0) :
    Nonempty (RelativeDehnCut D W eps q K.boundaryWord) := by
  apply exists_relativeDehnCut_of_certificate D hsc hmu hrho K q
  · intro relator hrelator
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨relator, hrelator, rfl⟩
  · exact hrot

end HullSC
end GroupApproximation
