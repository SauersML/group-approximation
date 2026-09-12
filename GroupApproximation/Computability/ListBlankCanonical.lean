import Mathlib.Computability.TuringMachine.Tape
import Mathlib.Data.List.Induction
import Mathlib.Logic.Equiv.Defs

/-!
# Canonical list representatives for half-tapes

`Turing.ListBlank Γ` is `List Γ` modulo appending and deleting trailing blanks,
so its constructor `Turing.ListBlank.mk` is surjective but far from injective:
`[]`, `[default]` and `[default, default]` are three names for one half-tape.
A half-tape therefore *is not* a list, and every construction that wants to read
a list off one --- an encoding of a tape as a word in a presentation, a length,
a decision procedure --- must first choose a representative.  Mathlib supplies
no such choice, and a choice that is not canonical is useless downstream: two
equal half-tapes have to produce the same word.

This file supplies the canonical choice.  Call a list *blank-reduced*
(`NoTrailingBlank`) when it does not end in a blank.  Two facts make that a
normal form:

* `mk_injOn`: `ListBlank.mk` is injective on blank-reduced lists.  The whole
  content is that `Turing.BlankRel` is not an opaque equivalence --- it exhibits
  one of the two lists as the other followed by a block of blanks, and a
  nonempty block of blanks is exactly a trailing blank.  So the only way two
  blank-reduced lists can be related is by an empty block.
* `exists_canonical`: every half-tape is named by exactly one blank-reduced
  list.

Existence is proved by induction from the *right* end of the list, peeling off
one trailing blank at a time, and needs no decidable equality: the alphabet is
arbitrary.  When the alphabet does have decidable equality the representative is
computed rather than chosen, by `trim`, and `toList` pushes `trim` through the
quotient --- well defined precisely because `trim` lands in blank-reduced lists,
where `mk` is injective.  `equivNoTrailingBlank` packages the result as an
explicit bijection between `ListBlank Γ` and the blank-reduced lists, which is
the sense in which a half-tape may be identified with a specific list.
-/

open Turing

namespace GroupApproximation.Turing

variable {Γ : Type*} [Inhabited Γ]

/-- A list is *blank-reduced* when it does not end in the blank symbol.  This is
the property that singles out one list in each `Turing.BlankRel` class: such a
class is a chain, each member an extension by blanks of the one below it, and
only the bottom member avoids a trailing blank.  The empty list is blank-reduced
because it has no last element at all. -/
def NoTrailingBlank (l : List Γ) : Prop :=
  l.getLast? ≠ some (default : Γ)

/-- The empty list is blank-reduced, having no last element to inspect. -/
theorem noTrailingBlank_nil : NoTrailingBlank ([] : List Γ) := by
  simp [NoTrailingBlank]

/-- Appending a nonempty block of blanks creates a trailing blank.  This is the
one computation behind everything below. -/
theorem getLast?_append_replicate (l : List Γ) {n : ℕ} (hn : n ≠ 0) :
    (l ++ List.replicate n (default : Γ)).getLast? = some default := by
  simp [List.getLast?_replicate, hn]

/-- A blank-reduced list is the shortest member of its class: if `l` is extended
by blanks to a blank-reduced `m`, then no blanks were added at all. -/
theorem eq_of_blankExtends {l m : List Γ} (h : BlankExtends l m)
    (hm : NoTrailingBlank m) : l = m := by
  obtain ⟨n, rfl⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact absurd (getLast?_append_replicate l hn.ne') hm

/-- Lists naming the same half-tape are `Turing.BlankRel`; this is
`Quotient.exact` for the blank setoid, stated in terms of `ListBlank.mk`. -/
theorem blankRel_of_mk_eq {l m : List Γ} (h : ListBlank.mk l = ListBlank.mk m) :
    BlankRel l m :=
  Quotient.exact' h

/-- `Turing.BlankRel` lists name the same half-tape; this is `Quotient.sound` for
the blank setoid, stated in terms of `ListBlank.mk`. -/
theorem mk_eq_mk_of_blankRel {l m : List Γ} (h : BlankRel l m) :
    ListBlank.mk l = ListBlank.mk m :=
  Quotient.sound' h

/-- Extending by blanks does not change the half-tape. -/
theorem mk_eq_mk_of_blankExtends {l m : List Γ} (h : BlankExtends l m) :
    ListBlank.mk l = ListBlank.mk m :=
  mk_eq_mk_of_blankRel (Or.inl h)

/-- **Uniqueness of canonical representatives.**  `ListBlank.mk` is injective on
blank-reduced lists, so a half-tape determines its blank-reduced name.  The
relation between the two lists points one way or the other, and either way
`eq_of_blankExtends` says the block of added blanks is empty. -/
theorem mk_injOn {l m : List Γ} (hl : NoTrailingBlank l) (hm : NoTrailingBlank m)
    (h : ListBlank.mk l = ListBlank.mk m) : l = m := by
  rcases blankRel_of_mk_eq h with he | he
  · exact eq_of_blankExtends he hm
  · exact (eq_of_blankExtends he hl).symm

/-- Prepending to a blank-reduced list keeps it blank-reduced, provided the new
symbol is not itself a lone trailing blank. -/
theorem noTrailingBlank_cons {a : Γ} :
    ∀ {l : List Γ}, NoTrailingBlank l → (l = [] → a ≠ default) → NoTrailingBlank (a :: l)
  | [], _, h => by
    show (a :: ([] : List Γ)).getLast? ≠ some default
    simpa using h rfl
  | _ :: _, h, _ => by
    show (a :: _ :: _).getLast? ≠ some default
    rw [List.getLast?_cons_cons]
    exact h

/-- **Existence of canonical representatives**, before passing to the quotient:
every list is an extension by blanks of a blank-reduced one.  The induction runs
from the right end, deleting a trailing blank when it finds one and stopping
otherwise; no decidable equality on the alphabet is needed, since the case split
happens inside a proof. -/
theorem exists_noTrailingBlank_blankExtends (l : List Γ) :
    ∃ m, NoTrailingBlank m ∧ BlankExtends m l := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], noTrailingBlank_nil, BlankExtends.refl _⟩
  | append_singleton l a ih =>
    by_cases ha : a = default
    · obtain ⟨m, hm, hext⟩ := ih
      refine ⟨m, hm, hext.trans ⟨1, ?_⟩⟩
      simp [ha]
    · refine ⟨l ++ [a], ?_, BlankExtends.refl _⟩
      show (l ++ [a]).getLast? ≠ some default
      rw [List.getLast?_concat]
      simpa using ha

/-- **Canonical representatives.**  Every half-tape is named by exactly one
blank-reduced list, so `ListBlank Γ` may be identified with the type of
blank-reduced lists over `Γ`. -/
theorem exists_canonical (L : ListBlank Γ) :
    ∃! l : List Γ, NoTrailingBlank l ∧ ListBlank.mk l = L := by
  induction L using Turing.ListBlank.induction_on with
  | h a =>
    obtain ⟨m, hm, hext⟩ := exists_noTrailingBlank_blankExtends a
    have hmk : ListBlank.mk m = ListBlank.mk a := mk_eq_mk_of_blankExtends hext
    refine ⟨m, ⟨hm, hmk⟩, ?_⟩
    rintro l ⟨hl, hlm⟩
    exact mk_injOn hl hm (hlm.trans hmk.symm)

section Trim

variable [DecidableEq Γ]

/-- Delete the trailing blanks of a list.

The recursion runs from the left, which looks backwards for an operation on the
right end, but it is the one that recurses structurally: `a :: l` keeps its head
unless the trimmed tail is empty *and* the head is itself a blank, in which case
the whole list was blanks.  Going from the left this way avoids the reversals
that `List.rdropWhile` needs and keeps every proof below a one-step induction. -/
def trim : List Γ → List Γ
  | [] => []
  | a :: l => if trim l = [] ∧ a = default then [] else a :: trim l

/-- Trimming the empty list. -/
@[simp]
theorem trim_nil : trim ([] : List Γ) = [] := rfl

/-- The defining equation of `trim` on a cons. -/
@[simp] theorem trim_cons (a : Γ) (l : List Γ) :
    trim (a :: l) = if trim l = [] ∧ a = default then [] else a :: trim l := rfl

/-- `trim` lands in blank-reduced lists: that is what it is for. -/
theorem noTrailingBlank_trim (l : List Γ) : NoTrailingBlank (trim l) := by
  induction l with
  | nil => exact noTrailingBlank_nil
  | cons a l ih =>
    rw [trim_cons]
    by_cases h : trim l = [] ∧ a = default
    · rw [if_pos h]
      exact noTrailingBlank_nil
    · rw [if_neg h]
      exact noTrailingBlank_cons ih fun he ha => h ⟨he, ha⟩

/-- `trim` only deletes blanks: the original list is the trimmed one followed by
a block of blanks. -/
theorem blankExtends_trim (l : List Γ) : BlankExtends (trim l) l := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons a l ih =>
    obtain ⟨n, hn⟩ := ih
    rw [trim_cons]
    by_cases h : trim l = [] ∧ a = default
    · refine ⟨n + 1, ?_⟩
      have hl : l = List.replicate n (default : Γ) := by rw [hn, h.1, List.nil_append]
      rw [if_pos h, h.2, hl, List.nil_append, List.replicate_succ]
    · refine ⟨n, ?_⟩
      rw [if_neg h, List.cons_append, ← hn]

/-- Trimming does not change the half-tape a list names. -/
theorem mk_trim (l : List Γ) : ListBlank.mk (trim l) = ListBlank.mk l :=
  mk_eq_mk_of_blankExtends (blankExtends_trim l)

/-- A list with no trailing blank has nothing to trim.  This is the first place
uniqueness is used: `trim l` and `l` are two blank-reduced names for one
half-tape, hence equal. -/
theorem trim_eq_self {l : List Γ} (h : NoTrailingBlank l) : trim l = l :=
  mk_injOn (noTrailingBlank_trim l) h (mk_trim l)

/-- `trim` is idempotent. -/
theorem trim_trim (l : List Γ) : trim (trim l) = trim l :=
  trim_eq_self (noTrailingBlank_trim l)

/-- Being blank-reduced is decidable when equality of symbols is. -/
instance (l : List Γ) : Decidable (NoTrailingBlank l) :=
  inferInstanceAs (Decidable (l.getLast? ≠ some (default : Γ)))

/-- The canonical list representative of a half-tape.  `trim` is constant on
each blank class --- two related lists trim to blank-reduced names of the same
half-tape, and `mk_injOn` identifies those --- so it descends to the quotient. -/
def toList (L : ListBlank Γ) : List Γ :=
  Quotient.liftOn' L trim fun a b h =>
    mk_injOn (noTrailingBlank_trim a) (noTrailingBlank_trim b) <| by
      rw [mk_trim, mk_trim]
      exact mk_eq_mk_of_blankRel h

/-- On a list, `toList` is `trim`. -/
@[simp]
theorem toList_mk (l : List Γ) : toList (ListBlank.mk l) = trim l := rfl

/-- The canonical representative is blank-reduced. -/
theorem noTrailingBlank_toList (L : ListBlank Γ) : NoTrailingBlank (toList L) := by
  induction L using Turing.ListBlank.induction_on with
  | h a => exact noTrailingBlank_trim a

/-- The canonical representative names the half-tape it came from. -/
@[simp]
theorem mk_toList (L : ListBlank Γ) : ListBlank.mk (toList L) = L := by
  induction L using Turing.ListBlank.induction_on with
  | h a => exact mk_trim a

/-- Half-tapes *are* the blank-reduced lists.  This is the statement the whole
file exists for: a `ListBlank Γ` may be replaced by a specific `List Γ`, and the
replacement is a bijection, not merely a section of `ListBlank.mk`. -/
def equivNoTrailingBlank : ListBlank Γ ≃ {l : List Γ // NoTrailingBlank l} where
  toFun L := ⟨toList L, noTrailingBlank_toList L⟩
  invFun l := ListBlank.mk l.1
  left_inv L := mk_toList L
  right_inv l := Subtype.ext (trim_eq_self l.2)

end Trim

end GroupApproximation.Turing
