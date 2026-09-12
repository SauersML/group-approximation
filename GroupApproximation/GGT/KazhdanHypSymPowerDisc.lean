import GroupApproximation.GGT.KazhdanHypSymmetrizedFilling
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Power discs over the symmetrized family

`GirthEightVKInterface.PowerDisc` and `GirthEightPrimitives2.PowerDiscCandidate`
fill a literal power `wⁿ` by a disc over the positive triangle words, which
cannot fill words of negative degree (`KazhdanHypLiteralFillingDegree`).  This
file restates both over `symTriangleRelatorWords T`, with the relator-only field
spelled `VanKampen.RelatorCellCover`.

* `SymPowerDisc T g n`, `SymPowerDiscCandidate T g n`, and the conversions
  `SymPowerDiscCandidate.toSymPowerDisc`, `SymPowerDisc.toCandidate`.
* `nonempty_symPowerDisc_of_symmetrizedLeastDisc`: **least symmetrized discs
  give power discs.**  At `g ≠ 1` with `gⁿ = 1` and `0 < n`, a representative
  word of `g` repeated `n` times is a nonempty null word, and
  `SymmetrizedLeastDisc T` fills it by a reduced covered disc.
* `nonempty_symPowerDisc_of_symmetrizedLiteralFilling`: the same from P1.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSymPowerDisc

open GroupApproximation.KazhdanHyp
open KazhdanHypSymmetrizedFilling

/-! ## Repeated words -/

section Words

variable {α : Type*}

/-- A word repeated `n` times spells the `n`-th power. -/
theorem mk_flatten_replicate (w : List (α × Bool)) :
    ∀ n : ℕ, FreeGroup.mk (List.replicate n w).flatten = FreeGroup.mk w ^ n
  | 0 => by
    show FreeGroup.mk [] = FreeGroup.mk w ^ 0
    rw [pow_zero, FreeGroup.one_eq_mk]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk,
      mk_flatten_replicate w n, pow_succ']

theorem map_flatten_replicate {β : Type*} (f : α → β) (w : List α) (n : ℕ) :
    ((List.replicate n w).flatten).map f = (List.replicate n (w.map f)).flatten := by
  rw [List.map_flatten, List.map_replicate]

theorem flatten_replicate_ne_nil {w : List α} (hw : w ≠ []) {n : ℕ} (hn : 0 < n) :
    (List.replicate n w).flatten ≠ [] := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m =>
    rw [List.replicate_succ, List.flatten_cons]
    exact fun h => hw (List.append_eq_nil_iff.mp h).1

end Words

/-! ## Power discs -/

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- A reduced relator-covered disc over the symmetrized family whose exterior is
a literal word repeated `n` times. -/
structure SymPowerDisc
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ) where
  /-- A literal signed word representing `g`. -/
  word : List (TriangularHodgeLayer.SignedGenerator Generator)
  /-- The word maps to the chosen presented-group element. -/
  represents : PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = g
  /-- A reduced disc for the repeated boundary word. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T)
  /-- The stored exterior traversal is the concatenation of `n` copies. -/
  boundary_eq : diagram.boundaryWord =
    (List.replicate n (word.map signedFreeRelLetter)).flatten
  /-- The disc is diagram-reduced. -/
  reduced : diagram.Reduced
  /-- Every inner face is a stored relator cell. -/
  relatorOnly : VanKampen.RelatorCellCover diagram

/-- A relator-covered filling over the symmetrized family of a literal power
boundary, before reducedness. -/
structure SymPowerDiscCandidate
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ) where
  /-- A literal signed word representing `g`. -/
  word : List (TriangularHodgeLayer.SignedGenerator Generator)
  /-- The word maps to the chosen presented-group element. -/
  represents : PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = g
  /-- Filling diagram. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T)
  /-- Its exterior is the literal `n`-fold repetition. -/
  boundary_eq : diagram.boundaryWord =
    (List.replicate n (word.map signedFreeRelLetter)).flatten
  /-- Every inner face is a stored relator cell. -/
  relatorOnly : VanKampen.RelatorCellCover diagram

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {g : TriangularHodgeLayer.Presented T} {n : ℕ}

/-- A reduced candidate is a power disc. -/
def SymPowerDiscCandidate.toSymPowerDisc (D : SymPowerDiscCandidate T g n)
    (hred : D.diagram.Reduced) : SymPowerDisc T g n where
  word := D.word
  represents := D.represents
  diagram := D.diagram
  boundary_eq := D.boundary_eq
  reduced := hred
  relatorOnly := D.relatorOnly

/-- A power disc is a candidate. -/
def SymPowerDisc.toCandidate (D : SymPowerDisc T g n) : SymPowerDiscCandidate T g n where
  word := D.word
  represents := D.represents
  diagram := D.diagram
  boundary_eq := D.boundary_eq
  relatorOnly := D.relatorOnly

/-- Every element of a triangularly presented group has a literal signed-word
representative. -/
theorem exists_signedWord_represents (g : TriangularHodgeLayer.Presented T) :
    ∃ word : List (TriangularHodgeLayer.SignedGenerator Generator),
      PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g := by
  obtain ⟨x, hx⟩ := PresentedGroup.mk_surjective
    (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) g
  refine ⟨x.toWord, ?_⟩
  rw [PresentedGroupRelatorReplay.word, FreeGroup.mk_toWord]
  exact hx

/-- **Least symmetrized discs give power discs.** -/
theorem nonempty_symPowerDisc_of_symmetrizedLeastDisc (hleast : SymmetrizedLeastDisc T)
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1) :
    Nonempty (SymPowerDisc T g n) := by
  obtain ⟨word, hword⟩ := exists_signedWord_represents g
  have hwne : word ≠ [] := by
    rintro rfl
    apply hne
    rw [← hword, PresentedGroupRelatorReplay.word, ← FreeGroup.one_eq_mk, map_one]
  have h1 : PresentedGroupRelatorReplay.word (List.replicate n word).flatten =
      PresentedGroupRelatorReplay.word word ^ n :=
    mk_flatten_replicate word n
  have hpw : PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word (List.replicate n word).flatten) = 1 := by
    rw [h1, map_pow, hword, hpow]
  obtain ⟨Delta, hbd, hcover, hred, -⟩ :=
    hleast _ (flatten_replicate_ne_nil hwne hn) hpw
  exact ⟨{
    word := word
    represents := hword
    diagram := Delta
    boundary_eq := by rw [hbd, map_flatten_replicate]
    reduced := hred
    relatorOnly := hcover }⟩

/-- **P1 gives power discs.** -/
theorem nonempty_symPowerDisc_of_symmetrizedLiteralFilling
    (hfill : SymmetrizedLiteralFilling T) (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1) :
    Nonempty (SymPowerDisc T g n) :=
  nonempty_symPowerDisc_of_symmetrizedLeastDisc
    (symmetrizedLeastDisc_of_symmetrizedLiteralFilling hfill) hn hpow hne

end Table

end KazhdanHypSymPowerDisc
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypSymPowerDisc.mk_flatten_replicate
#audit_axioms GroupApproximation.GGT.KazhdanHypSymPowerDisc.nonempty_symPowerDisc_of_symmetrizedLeastDisc
#audit_axioms GroupApproximation.GGT.KazhdanHypSymPowerDisc.nonempty_symPowerDisc_of_symmetrizedLiteralFilling
