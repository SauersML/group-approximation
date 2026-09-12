import GroupApproximation.Algebra.CoprodIAltWord

/-!
# Normalizing binary free-product syllables

A raw two-factor spelling is easier to construct with an ordinary inductive
type than with dependent sigma terms.  This module merges adjacent syllables
from the same factor, drops identity products, proves evaluation unchanged,
and packages the resulting alternating nontrivial list as `CoprodI.Word`.
-/

namespace GroupApproximation
namespace BinarySyllableNormalizer

open Monoid Monoid.CoprodI

universe u

variable {L R : Type u} [Group L] [Group R]

inductive Syllable (L R : Type u)
  | row : L → Syllable L R
  | code : R → Syllable L R

abbrev Factor (L R : Type u) : Bool → Type u
  | false => L
  | true => R

@[reducible] instance factorGroup (i : Bool) : Group (Factor L R i) := by
  cases i <;> simp only [Factor] <;> infer_instance

def Syllable.tag : Syllable L R → Bool
  | .row _ => false
  | .code _ => true

def Syllable.Nontrivial : Syllable L R → Prop
  | .row x => x ≠ 1
  | .code x => x ≠ 1

def Syllable.toSigma : Syllable L R → Σ i, Factor L R i
  | .row x => ⟨false, x⟩
  | .code x => ⟨true, x⟩

def eval : Syllable L R → CoprodI (Factor L R)
  | .row x => CoprodI.of (i := false) x
  | .code x => CoprodI.of (i := true) x

@[simp] theorem of_row_mul (x y : L) :
    CoprodI.of (M := Factor L R) (i := false) x *
        CoprodI.of (M := Factor L R) (i := false) y =
      CoprodI.of (M := Factor L R) (i := false) (x * y) :=
  (map_mul (CoprodI.of (M := Factor L R) (i := false)) x y).symm

@[simp] theorem of_code_mul (x y : R) :
    CoprodI.of (M := Factor L R) (i := true) x *
        CoprodI.of (M := Factor L R) (i := true) y =
      CoprodI.of (M := Factor L R) (i := true) (x * y) :=
  (map_mul (CoprodI.of (M := Factor L R) (i := true)) x y).symm

def evalList (l : List (Syllable L R)) : CoprodI (Factor L R) :=
  (l.map eval).prod

def Normal (l : List (Syllable L R)) : Prop :=
  (∀ s ∈ l, s.Nontrivial) ∧
    l.IsChain fun s t => s.tag ≠ t.tag

/-- Insert one syllable into an already normalized tail. -/
noncomputable def prepend : Syllable L R → List (Syllable L R) →
    List (Syllable L R) := by
  classical
  exact fun
    | .row x, [] => if x = 1 then [] else [.row x]
    | .code x, [] => if x = 1 then [] else [.code x]
    | .row x, .row y :: l =>
        if x * y = 1 then l else .row (x * y) :: l
    | .code x, .code y :: l =>
        if x * y = 1 then l else .code (x * y) :: l
    | .row x, .code y :: l =>
        if x = 1 then .code y :: l else .row x :: .code y :: l
    | .code x, .row y :: l =>
        if x = 1 then .row y :: l else .code x :: .row y :: l

noncomputable def normalize : List (Syllable L R) → List (Syllable L R) :=
  List.foldr prepend []

@[simp] theorem normalize_nil : normalize ([] : List (Syllable L R)) = [] := rfl

theorem normalize_cons (s : Syllable L R) (l : List (Syllable L R)) :
    normalize (s :: l) = prepend s (normalize l) := rfl

theorem normalize_append (l₁ l₂ : List (Syllable L R)) :
    normalize (l₁ ++ l₂) = List.foldr prepend (normalize l₂) l₁ := by
  simp [normalize, List.foldr_append]

theorem length_prepend_le (s : Syllable L R) (l : List (Syllable L R)) :
    (prepend s l).length ≤ l.length + 1 := by
  cases s with
  | row x =>
      cases l with
      | nil => by_cases hx : x = 1 <;> simp [prepend, hx]
      | cons q l =>
          cases q with
          | row y =>
              by_cases hxy : x * y = 1
              · simp [prepend, hxy]
                omega
              · simp [prepend, hxy]
          | code y => by_cases hx : x = 1 <;> simp [prepend, hx]
  | code x =>
      cases l with
      | nil => by_cases hx : x = 1 <;> simp [prepend, hx]
      | cons q l =>
          cases q with
          | row y => by_cases hx : x = 1 <;> simp [prepend, hx]
          | code y =>
              by_cases hxy : x * y = 1
              · simp [prepend, hxy]
                omega
              · simp [prepend, hxy]

theorem length_normalize_le (l : List (Syllable L R)) :
    (normalize l).length ≤ l.length := by
  induction l with
  | nil => simp [normalize]
  | cons s l ih =>
      simp only [normalize, List.foldr_cons, List.length_cons]
      exact le_trans (length_prepend_le s (List.foldr prepend [] l))
        (Nat.add_le_add_right ih 1)

@[simp] theorem evalList_nil : evalList ([] : List (Syllable L R)) = 1 := rfl

@[simp] theorem evalList_cons (s : Syllable L R) (l : List (Syllable L R)) :
    evalList (s :: l) = eval s * evalList l := by
  simp [evalList]

theorem eval_prepend (s : Syllable L R) (l : List (Syllable L R)) :
    evalList (prepend s l) = eval s * evalList l := by
  cases s with
  | row x =>
      cases l with
      | nil =>
          by_cases hx : x = 1 <;> simp [prepend, hx, eval]
      | cons q l =>
          cases q with
          | row y =>
              by_cases hxy : x * y = 1
              · simp only [prepend, if_pos hxy, evalList_cons, eval]
                rw [← mul_assoc, of_row_mul, hxy]
                change evalList l =
                  CoprodI.of (M := Factor L R) (i := false) (1 : L) * evalList l
                rw [map_one, one_mul]
              · simp [prepend, hxy, eval, mul_assoc]
          | code y =>
              by_cases hx : x = 1 <;> simp [prepend, hx, eval]
  | code x =>
      cases l with
      | nil =>
          by_cases hx : x = 1 <;> simp [prepend, hx, eval]
      | cons q l =>
          cases q with
          | row y =>
              by_cases hx : x = 1 <;> simp [prepend, hx, eval]
          | code y =>
              by_cases hxy : x * y = 1
              · simp only [prepend, if_pos hxy, evalList_cons, eval]
                rw [← mul_assoc, of_code_mul, hxy]
                change evalList l =
                  CoprodI.of (M := Factor L R) (i := true) (1 : R) * evalList l
                rw [map_one, one_mul]
              · simp [prepend, hxy, eval, mul_assoc]

theorem normal_prepend (s : Syllable L R) {l : List (Syllable L R)}
    (hl : Normal l) : Normal (prepend s l) := by
  rcases hl with ⟨hne, halt⟩
  cases s with
  | row x =>
      cases l with
      | nil =>
          by_cases hx : x = 1 <;> simp [prepend, hx, Normal, Syllable.Nontrivial]
      | cons q l =>
          cases q with
          | row y =>
              have htail : Normal l := ⟨fun z hz => hne z (by simp [hz]), halt.tail⟩
              by_cases hxy : x * y = 1
              · simpa [prepend, hxy] using htail
              · refine ⟨?_, ?_⟩
                · intro z hz
                  simp only [prepend, if_neg hxy, List.mem_cons] at hz
                  rcases hz with rfl | hz
                  · exact hxy
                  · exact htail.1 z hz
                · simp only [prepend, hxy, if_false]
                  cases l with
                  | nil => exact List.IsChain.singleton _
                  | cons z l =>
                      rw [List.isChain_cons_cons] at halt ⊢
                      exact ⟨halt.1, halt.2⟩
          | code y =>
              by_cases hx : x = 1
              · simpa [prepend, hx] using ⟨hne, halt⟩
              · refine ⟨?_, ?_⟩
                · intro z hz
                  simp only [prepend, if_neg hx, List.mem_cons] at hz
                  rcases hz with rfl | hz
                  · exact hx
                  · exact hne z (by simpa only [List.mem_cons] using hz)
                · simp only [prepend, hx, if_false,
                    List.isChain_cons_cons]
                  exact ⟨by simp [Syllable.tag], halt⟩
  | code x =>
      cases l with
      | nil =>
          by_cases hx : x = 1 <;> simp [prepend, hx, Normal, Syllable.Nontrivial]
      | cons q l =>
          cases q with
          | row y =>
              by_cases hx : x = 1
              · simpa [prepend, hx] using ⟨hne, halt⟩
              · refine ⟨?_, ?_⟩
                · intro z hz
                  simp only [prepend, if_neg hx, List.mem_cons] at hz
                  rcases hz with rfl | hz
                  · exact hx
                  · exact hne z (by simpa only [List.mem_cons] using hz)
                · simp only [prepend, hx, if_false,
                    List.isChain_cons_cons]
                  exact ⟨by simp [Syllable.tag], halt⟩
          | code y =>
              have htail : Normal l := ⟨fun z hz => hne z (by simp [hz]), halt.tail⟩
              by_cases hxy : x * y = 1
              · simpa [prepend, hxy] using htail
              · refine ⟨?_, ?_⟩
                · intro z hz
                  simp only [prepend, if_neg hxy, List.mem_cons] at hz
                  rcases hz with rfl | hz
                  · exact hxy
                  · exact htail.1 z hz
                · simp only [prepend, hxy, if_false]
                  cases l with
                  | nil => exact List.IsChain.singleton _
                  | cons z l =>
                      rw [List.isChain_cons_cons] at halt ⊢
                      exact ⟨halt.1, halt.2⟩

theorem normal_normalize (l : List (Syllable L R)) : Normal (normalize l) := by
  induction l with
  | nil => simp [normalize, Normal]
  | cons s l ih =>
      simpa [normalize] using normal_prepend s ih

theorem eval_normalize (l : List (Syllable L R)) :
    evalList (normalize l) = evalList l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      rw [normalize_cons, eval_prepend]
      rw [ih, evalList_cons]

omit [Group L] [Group R] in theorem chain_toSigma {l : List (Syllable L R)}
    (h : l.IsChain fun s t => s.tag ≠ t.tag) :
    (l.map Syllable.toSigma).IsChain fun p q => p.1 ≠ q.1 := by
  induction l with
  | nil => exact List.isChain_nil
  | cons s l ih =>
      cases l with
      | nil => exact List.IsChain.singleton _
      | cons t l =>
          rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
          rw [List.isChain_cons_cons] at h
          refine ⟨?_, ih h.2⟩
          cases s <;> cases t <;>
            simp_all [Syllable.tag, Syllable.toSigma]

/-- The normalized list as Mathlib's canonical reduced-word carrier. -/
noncomputable def normalizedWord (l : List (Syllable L R)) :
    CoprodI.Word (Factor L R) where
  toList := (normalize l).map Syllable.toSigma
  ne_one := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
    have hn := (normal_normalize l).1 s hs
    cases s with
    | row x =>
        change x ≠ (1 : L) at hn
        change x ≠ (1 : L)
        exact hn
    | code x =>
        change x ≠ (1 : R) at hn
        change x ≠ (1 : R)
        exact hn
  chain_ne := chain_toSigma (normal_normalize l).2

theorem normalizedWord_prod (l : List (Syllable L R)) :
    (normalizedWord l).prod = evalList l := by
  change CoprodIAltWord.listProd
      ((normalize l).map Syllable.toSigma) = evalList l
  rw [← eval_normalize]
  unfold CoprodIAltWord.listProd evalList
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  cases s <;> rfl

end BinarySyllableNormalizer
end GroupApproximation
