import GroupApproximation.GGT.HullSCLemma44FamilyAssembly
import GroupApproximation.GGT.HullSCRelatorFamily

/-!
# Hull's relator re-spelled over the original peripheral family

The joint family reads Hull's relator by relabelling its index, so nothing
changes.  The original family cannot: the selected peripheral letters are not
letters there, and every one of them has to be spelled by a word over the
original relative alphabet.  Lengths change, so the small-cancellation
parameters change with them.

This file separates the bookkeeping from the estimate.  `expandWord` spells a
selected word letter by letter and concatenates; it preserves the spelled
element, keeps every letter legal, and only lengthens.  Those three facts, plus
the one-relator symmetrization machinery of `HullSCRelatorFamily`, reduce the
original half of the re-spelling to `OriginalRelatorExpansion`: an expanded
relator together with the four metric clauses -- depth, pieces, published
pieces, and the quasi-geodesic chain -- for that one word.

Everything else is discharged here: the relator family is the symmetrized
closure of the expanded word, its closure clauses are the `Sym` constructors,
its strong boundedness is finiteness of a finite word's letters, and its normal
closure agrees with the source one because the expansion spells the same
element.

`originalRelatorExpansion_nil` is the model test: the empty relator has an
expansion, so the residue is not vacuous.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Expanding a selected word over the original alphabet -/

section Expansion

variable {G : Type u} [Group G] {Lambda : Type w} {k : ℕ}

/-- Spell every letter of a selected word over the original alphabet and
concatenate the results. -/
def expandWord
    (spell : GGT.RelLetter G (AuxiliaryPeripheralIndex k) →
      List (GGT.RelLetter G Lambda)) :
    List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)) →
      List (GGT.RelLetter G Lambda)
  | [] => []
  | a :: t => spell a ++ expandWord spell t

/-- The expansion spells the same group element. -/
theorem listVal_expandWord
    (spell : GGT.RelLetter G (AuxiliaryPeripheralIndex k) →
      List (GGT.RelLetter G Lambda))
    (hspell : ∀ a, GGT.RelLetter.listVal (spell a) = a.val)
    (v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) :
    GGT.RelLetter.listVal (expandWord spell v) =
      GGT.RelLetter.listVal v := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      show GGT.RelLetter.listVal (spell a ++ expandWord spell t) =
        GGT.RelLetter.listVal (a :: t)
      rw [RelWord.listVal_append, ih, hspell a,
        GGT.OsinComponents.listVal_cons]

/-- Every letter of the expansion is a letter of the original family. -/
theorem letters_expandWord
    {original : GGT.RelGenSet G Lambda}
    (spell : GGT.RelLetter G (AuxiliaryPeripheralIndex k) →
      List (GGT.RelLetter G Lambda))
    (hletters : ∀ a b, b ∈ spell a → original.IsLetter b)
    (v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) :
    ∀ b ∈ expandWord spell v, original.IsLetter b := by
  induction v with
  | nil =>
      intro b hb
      simp [expandWord] at hb
  | cons a t ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hletters a b hb
      · exact ih b hb

omit [Group G] in
/-- The expansion is at least as long as the source word, provided no letter is
spelled by the empty word. -/
theorem length_le_length_expandWord
    (spell : GGT.RelLetter G (AuxiliaryPeripheralIndex k) →
      List (GGT.RelLetter G Lambda))
    (hne : ∀ a, 1 ≤ (spell a).length)
    (v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) :
    v.length ≤ (expandWord spell v).length := by
  induction v with
  | nil => simp [expandWord]
  | cons a t ih =>
      show (a :: t).length ≤ (spell a ++ expandWord spell t).length
      rw [List.length_cons, List.length_append]
      have := hne a
      omega

end Expansion

/-! ## The residual estimate for one relator -/

/-- **What is left of the original half of the re-spelling.**

An expanded relator over the original alphabet, together with the four metric
clauses for that single word.  The bookkeeping clauses of `C(eps, mu, rho)` are
not asked for: closure under rotation and inversion, admissibility and length of
the whole symmetrized family, its strong boundedness, and the agreement of the
normal closures are all supplied by `relatorRespellingAt_original_of_expansion`.

The depth clause is stated for the letter and for its inverse, which is what
`RelWord.isSmallCancellation_symmetrized` consumes. -/
structure OriginalRelatorExpansion {G : Type u} [Group G] {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda) {k : ℕ}
    (v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))
    (eps rho : ℕ) (mu : ℝ) where
  /-- The relator spelled over the original relative alphabet. -/
  word : List (GGT.RelLetter G Lambda)
  /-- Osin's relative generating sets are symmetric. -/
  base_inv : ∀ g ∈ original.base, g⁻¹ ∈ original.base
  /-- Every letter of the expansion is legal. -/
  letters : ∀ b ∈ word, original.IsLetter b
  /-- The expansion spells the same element, so it presents the same
  quotient. -/
  value : GGT.RelLetter.listVal word = GGT.RelLetter.listVal v
  /-- The expansion is long. -/
  long : rho ≤ word.length
  /-- Every peripheral letter of the expansion is deep in its own relative
  metric, together with its inverse. -/
  deep : ∀ b ∈ word, ∀ lam : Lambda, GGT.RelLetter.IsCompOf lam b →
    b.val ∉ original.relBall lam rho ∧
      (b.val)⁻¹ ∉ original.relBall lam rho
  /-- Pieces of the expanded family are short. -/
  pieces : ∀ u w : List (GGT.RelLetter G Lambda),
    RelWord.IsPiece original (RelWord.symmetrized word) eps u w →
      (u.length : ℝ) < mu * w.length
  /-- Published pieces of the expanded family are short. -/
  published : ∀ u u' w : List (GGT.RelLetter G Lambda),
    RelWord.IsPublishedPiece original (RelWord.symmetrized word) eps u u' w →
      max (u.length : ℝ) (u'.length : ℝ) < mu * w.length
  /-- The expanded relator is a quasi-geodesic chain in the original relative
  alphabet. -/
  quasiGeodesic : ∀ w ∈ RelWord.symmetrized word,
    GGT.IsQuasiGeodesicChainAt original.alphabet.carrier 4 1
      (fun i => GGT.RelLetter.listVal (w.take i)) w.length

namespace OriginalRelatorExpansion

variable {G : Type u} [Group G] {Lambda : Type w}
  {original : GGT.RelGenSet G Lambda} {k : ℕ}
  {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
  {eps rho : ℕ} {mu : ℝ}

/-- The expanded family is a Lemma 4.4 input.  The five bookkeeping clauses and
strong boundedness come from the one-relator symmetrization machinery. -/
theorem isLemma44Input (E : OriginalRelatorExpansion original v eps rho mu) :
    RelWord.IsLemma44Input original (RelWord.symmetrized E.word) eps mu rho :=
  RelWord.isLemma44Input_symmetrized_of original E.word eps mu rho
    (RelWord.isSmallCancellation_symmetrized E.base_inv E.letters E.long
      E.deep E.pieces)
    E.quasiGeodesic E.published

/-- The two families normally generate the same subgroup, because the expansion
spells the same element. -/
theorem normalClosure_eq (E : OriginalRelatorExpansion original v eps rho mu) :
    Subgroup.normalClosure
        (GGT.RelLetter.listVal '' RelWord.symmetrized E.word) =
      Subgroup.normalClosure
        (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
  rw [RelWord.normalClosure_listVal_image_symmetrized,
    RelWord.normalClosure_listVal_image_symmetrized, E.value]

end OriginalRelatorExpansion

/-- **The original half of the re-spelling, from the residual estimate.** -/
theorem relatorRespellingAt_original_of_expansion
    {G : Type u} [Group G] {Lambda : Type w}
    {original : GGT.RelGenSet G Lambda} {k : ℕ}
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (E : OriginalRelatorExpansion original v eps rho mu)
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho) :
    RelatorRespellingAt original (RelWord.symmetrized v) eps0 rho0 mu :=
  ⟨RelWord.symmetrized E.word, eps, rho, heps, hrho, h20,
    E.normalClosure_eq, E.isLemma44Input⟩

/-! ## Model test -/

/-- Model test: the empty relator has an expansion, so the residual estimate is
not vacuous.  Every clause is decided by the fact that the symmetrized closure
of the empty word is the empty word alone. -/
def originalRelatorExpansion_nil {G : Type u} [Group G] {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda) {k : ℕ}
    (hbase : ∀ g ∈ original.base, g⁻¹ ∈ original.base) (eps : ℕ) (mu : ℝ) :
    OriginalRelatorExpansion original
      ([] : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) eps 0 mu where
  word := []
  base_inv := hbase
  letters := by
    intro b hb
    simp at hb
  value := rfl
  long := by simp
  deep := by
    intro b hb
    simp at hb
  pieces := by
    intro u w hp
    obtain ⟨hw, -, w', hw', hne, -⟩ := hp
    have hw0 : w = [] :=
      List.length_eq_zero_iff.mp
        (by simpa using RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hw))
    have hw'0 : w' = [] :=
      List.length_eq_zero_iff.mp
        (by simpa using RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hw'))
    exact absurd (hw'0.trans hw0.symm) hne
  published := by
    intro u u' w hp
    obtain ⟨hw, -, w', hw', -, -, y, z, -, -, -, hexcl⟩ := hp
    have hw0 : w = [] :=
      List.length_eq_zero_iff.mp
        (by simpa using RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hw))
    have hw'0 : w' = [] :=
      List.length_eq_zero_iff.mp
        (by simpa using RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hw'))
    refine absurd ?_ hexcl
    rw [hw0, hw'0, GGT.RelLetter.listVal_nil]
    group
  quasiGeodesic := by
    intro w hw
    have hw0 : w = [] :=
      List.length_eq_zero_iff.mp
        (by simpa using RelWord.Sym.length_eq (RelWord.mem_symmetrized.mp hw))
    subst hw0
    intro i j hij hj
    have hj0 : j = 0 := by simpa using hj
    have hi0 : i = 0 := by omega
    subst hj0
    subst hi0
    refine ⟨?_, ?_⟩
    · rw [wordDist_self]
      norm_num
    · rw [wordDist_self]

end HullSC
end GroupApproximation
