import Mathlib.Computability.Primrec.List
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Words and one-query oracle reductions

Support for the section "Word problems" of `simple_kazhdan_sofic_group.tex`: the algebra of formal
words (append, inverse, commutator, image under a homomorphism), and the reduction pattern the
section uses twice: a function computed from one query to a total oracle, at a primitive recursive
position and with a primitive recursive answer map, is Turing reducible to that oracle.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Encodable

section Words

variable {ι H : Type*} [Group H] (s : ι → H)

/-- The formal inverse of a word. -/
def wordInv (w : List (ι × Bool)) : List (ι × Bool) :=
  (w.map fun x => (x.1, !x.2)).reverse

/-- The formal commutator `a b a⁻¹ b⁻¹` of two words. -/
def wordComm (a b : List (ι × Bool)) : List (ι × Bool) :=
  a ++ b ++ wordInv a ++ wordInv b

theorem wordValue_nil : wordValue s [] = 1 :=
  rfl

theorem wordValue_cons (x : ι × Bool) (w : List (ι × Bool)) :
    wordValue s (x :: w) = (if x.2 then s x.1 else (s x.1)⁻¹) * wordValue s w := by
  obtain ⟨i, b⟩ := x
  rfl

theorem wordValue_append (a b : List (ι × Bool)) :
    wordValue s (a ++ b) = wordValue s a * wordValue s b := by
  induction a with
  | nil => rw [List.nil_append, wordValue_nil, one_mul]
  | cons x a ih => rw [List.cons_append, wordValue_cons, wordValue_cons, ih, mul_assoc]

theorem wordValue_wordInv (w : List (ι × Bool)) : wordValue s (wordInv w) = (wordValue s w)⁻¹ := by
  induction w with
  | nil => rw [wordValue_nil, inv_one]; rfl
  | cons x w ih =>
    obtain ⟨i, b⟩ := x
    have h1 : wordInv ((i, b) :: w) = wordInv w ++ [(i, !b)] := by
      simp [wordInv]
    rw [h1, wordValue_append, ih, wordValue_cons, wordValue_cons, wordValue_nil, mul_one,
      mul_inv_rev]
    cases b <;> simp

theorem wordValue_wordComm (a b : List (ι × Bool)) :
    wordValue s (wordComm a b) =
      wordValue s a * wordValue s b * (wordValue s a)⁻¹ * (wordValue s b)⁻¹ := by
  rw [wordComm, wordValue_append, wordValue_append, wordValue_append, wordValue_wordInv,
    wordValue_wordInv]

/-- The value of a word in the images of the generators is the image of its value. -/
theorem wordValue_map {K : Type*} [Group K] (φ : H →* K) (w : List (ι × Bool)) :
    wordValue (φ ∘ s) w = φ (wordValue s w) := by
  induction w with
  | nil => rw [wordValue_nil, wordValue_nil, map_one]
  | cons x w ih =>
    obtain ⟨i, b⟩ := x
    rw [wordValue_cons, wordValue_cons, ih, map_mul]
    cases b <;> simp

/-- Composing the generators with an injective homomorphism does not change the word problem. -/
theorem wordProblemOracle_comp_injective [Primcodable ι] {K : Type*} [Group K] (φ : H →* K)
    (hφ : Function.Injective φ) : wordProblemOracle (φ ∘ s) = wordProblemOracle s := by
  have key : ∀ x : H, φ x = 1 ↔ x = 1 := fun x => by
    rw [← map_one φ]
    exact hφ.eq_iff
  funext n
  have hiff : (∃ w : List (ι × Bool), Encodable.decode n = some w ∧ wordValue (φ ∘ s) w = 1) ↔
      ∃ w : List (ι × Bool), Encodable.decode n = some w ∧ wordValue s w = 1 := by
    simp only [wordValue_map, key]
  simp only [wordProblemOracle]
  by_cases h₁ : ∃ w : List (ι × Bool), Encodable.decode n = some w ∧ wordValue (φ ∘ s) w = 1
  · rw [if_pos h₁, if_pos (hiff.1 h₁)]
  · rw [if_neg h₁, if_neg fun h => h₁ (hiff.2 h)]

end Words

section Oracle

/-- **One-query reduction.**  If `F n` is the answer map `g n` applied to the value of the total
oracle `o` at the position `f n`, with `f` and `g` primitive recursive, then `F ≤_T O`. -/
theorem turingReducible_of_query {F O : ℕ →. ℕ} (o : ℕ → ℕ) (hO : ∀ n, O n = Part.some (o n))
    (f : ℕ → ℕ) (g : ℕ → ℕ → ℕ) (hf : Primrec f) (hg : Primrec₂ g)
    (hF : ∀ n, F n = Part.some (g n (o (f n)))) : TuringReducible F O := by
  obtain rfl : O = fun n => Part.some (o n) := funext hO
  have hO' : Nat.RecursiveIn {fun n => Part.some (o n)} (fun n => Part.some (o n)) :=
    Nat.RecursiveIn.oracle _ (Set.mem_singleton _)
  have hfr : Nat.RecursiveIn {fun n => Part.some (o n)} (fun n => Part.some (f n)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.1 hf)
  have hq : Nat.RecursiveIn {fun n => Part.some (o n)} (fun n => Part.some (o (f n))) :=
    Nat.RecursiveIn.of_eq (Nat.RecursiveIn.comp hO' hfr) fun n => by
      simp only [Part.bind_eq_bind, Part.bind_some]
  have hid : Nat.RecursiveIn {fun n => Part.some (o n)} (fun n => Part.some n) :=
    Nat.Primrec.recursiveIn Nat.Primrec.id
  have hg' : Nat.RecursiveIn {fun n => Part.some (o n)}
      (fun p => Part.some (g (Nat.unpair p).1 (Nat.unpair p).2)) :=
    Nat.Primrec.recursiveIn (Primrec.nat_iff.1
      (hg.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
  refine RecursiveIn.iff_nat.2 (Nat.RecursiveIn.of_eq
    (Nat.RecursiveIn.comp hg' (Nat.RecursiveIn.pair hid hq)) fun n => ?_)
  rw [hF n]
  simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map, Part.map_some, Part.bind_some,
    Nat.unpair_pair]

end Oracle

#audit_axioms wordValue_wordComm
#audit_axioms wordProblemOracle_comp_injective
#audit_axioms turingReducible_of_query

end SimpleKazhdanSofic
end GroupApproximation
