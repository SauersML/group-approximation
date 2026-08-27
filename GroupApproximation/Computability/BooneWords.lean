import GroupApproximation.Computability.BooneTowerPresentation
import GroupApproximation.Computability.RawWord

/-!
# The Boone group's words, as raw data

`BooneTowerPresentation` presents the tower and gives it a numbering, so the
group is named by a `PresentationCode`.  What a reduction needs on top of that
is the *words*: for a machine configuration `(α, β)`, the element

    k⁻¹ · t(α,β) · k · t(α,β)⁻¹

whose triviality is Simpson's Theorem 8 criterion for halting.  This file writes
that element as a raw `List (ℕ × Bool)` and proves the code reads it as the
element it should.

Everything is explicit in `(α, β)`: `t(α,β) = (x^α y^β)⁻¹ t (x^α y^β)`, so the
raw word is built from `List.replicate` and the four generator indices, which is
what makes the map from configurations to words computable.
-/

namespace GroupApproximation
namespace BooneWords

open BooneGroup Base BooneBaseWords BooneTowerPresentation
open PresentationCodes PresentationCodeList RawWord PresentedGroupRelabel

variable {S : Stage} (P : StagePres S)

/-! ## Generator indices -/

/-- The number of the `i`-th base generator, in the stage's code. -/
def genIdx (i : BooneGroup.Gen) : ℕ :=
  ((P.enum (P.letterOfGen i) : Fin (P.gpred + 1)) : ℕ)

theorem letterOf_genIdx (i : BooneGroup.Gen) :
    letterOf (stageCode P) (genIdx P i) = P.enum (P.letterOfGen i) := by
  refine Fin.ext ?_
  show (genIdx P i) % (P.gpred + 1) = _
  rw [genIdx]
  exact Nat.mod_eq_of_lt (P.enum (P.letterOfGen i)).isLt

theorem wordOf_replicate (c : PresentationCode) (i : ℕ) :
    ∀ n : ℕ, wordOf c (List.replicate n (i, true)) = (FreeGroup.of (letterOf c i)) ^ n
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, wordOf_cons_pos, wordOf_replicate c i n, pow_succ']

/-! ## The words -/

/-- `x^α y^β`, as a raw word. -/
def rawSh (q : ℕ × ℕ) : List (ℕ × Bool) :=
  List.replicate q.1 (genIdx P 1, true) ++ List.replicate q.2 (genIdx P 2, true)

/-- `t(α,β) = (x^α y^β)⁻¹ t (x^α y^β)`, as a raw word. -/
def rawTw (q : ℕ × ℕ) : List (ℕ × Bool) :=
  invWord (rawSh P q) ++ (genIdx P 0, true) :: rawSh P q

theorem wordOf_rawSh (q : ℕ × ℕ) :
    wordOf (stageCode P) (rawSh P q)
      = relabel (P.enum : P.Letters → Fin (P.gpred + 1))
          (P.word (shWord ((q.1 : ℤ), (q.2 : ℤ)))) := by
  rw [rawSh, wordOf_append, wordOf_replicate, wordOf_replicate,
    letterOf_genIdx, letterOf_genIdx, shWord, map_mul, map_zpow, map_zpow,
    P.word_of, P.word_of, map_mul, map_zpow, map_zpow, FreeGroup.map.of,
    FreeGroup.map.of, zpow_natCast, zpow_natCast]
  rfl

theorem wordOf_rawTw (q : ℕ × ℕ) :
    wordOf (stageCode P) (rawTw P q)
      = relabel (P.enum : P.Letters → Fin (P.gpred + 1))
          (P.word (twWord ((q.1 : ℤ), (q.2 : ℤ)))) := by
  rw [rawTw, wordOf_append, wordOf_invWord, wordOf_cons_pos, wordOf_rawSh,
    letterOf_genIdx]
  simp only [twWord, map_mul, map_inv, P.word_of, FreeGroup.map.of]
  rw [mul_assoc]
  rfl

/-! ## The halting word

At the last layer the stable letter `k` is the new letter `none`, and the
element whose triviality is Simpson's halting criterion is
`k⁻¹ · t(α,β) · k · t(α,β)⁻¹`. -/

section Final

/-- The stable letter `k`, as a letter of the last stage.  Named rather than
written `none`, so its type is the stage's `Letters` and not the `Option` that
happens to unfold to it. -/
def kLetter : (finalPres P).Letters := none

/-- The number of the stable letter `k`. -/
noncomputable def kIdx : ℕ :=
  (((finalPres P).enum (kLetter P) : Fin ((finalPres P).gpred + 1)) : ℕ)

theorem letterOf_kIdx :
    letterOf (stageCode (finalPres P)) (kIdx P) = (finalPres P).enum (kLetter P) := by
  refine Fin.ext ?_
  show (kIdx P) % ((finalPres P).gpred + 1) = _
  rw [kIdx]
  exact Nat.mod_eq_of_lt ((finalPres P).enum (kLetter P)).isLt

/-- **The halting word**: `k⁻¹ · t(α,β) · k · t(α,β)⁻¹`, as raw data.
Everything in it is `List.replicate` and four fixed indices, so it is a
computable function of the configuration. -/
noncomputable def rawComm (q : ℕ × ℕ) : List (ℕ × Bool) :=
  (kIdx P, false) :: (rawTw (finalPres P) q ++
    (kIdx P, true) :: invWord (rawTw (finalPres P) q))

/-- The stable letter `k`, at the last stage.  Named at the *stage's* carrier
type: writing `HNNExtension.t` inline picks the `HNNExtension` multiplication
instance rather than the stage's, and the two are defeq but not syntactically
equal, which stops every `map_mul`. -/
noncomputable def kElt : (finalStage S P.tsub).Carrier := HNNExtension.t

/-- `t(α,β)`, at the last stage. -/
noncomputable def twElt (q : ℕ × ℕ) : (finalStage S P.tsub).Carrier :=
  (finalStage S P.tsub).ι (tw ((q.1 : ℤ), (q.2 : ℤ)))

/-- The element the word names. -/
noncomputable def commElt (q : ℕ × ℕ) : (finalStage S P.tsub).Carrier :=
  (kElt P)⁻¹ * twElt P q * kElt P * (twElt P q)⁻¹

/-- The presentation reads the halting word as the halting element. -/
theorem equiv_commElt (q : ℕ × ℕ) :
    (finalPres P).equiv (commElt P q)
      = PresentedGroup.mk (finalPres P).rels
          ((FreeGroup.of (kLetter P))⁻¹ *
            (finalPres P).word (twWord ((q.1 : ℤ), (q.2 : ℤ))) *
            FreeGroup.of (kLetter P) *
            ((finalPres P).word (twWord ((q.1 : ℤ), (q.2 : ℤ))))⁻¹) := by
  have ht : (finalPres P).equiv (kElt P) = PresentedGroup.of (kLetter P) :=
    finalEquivPres_t P
  have htw : (finalPres P).equiv (twElt P q)
      = PresentedGroup.mk (finalPres P).rels
          ((finalPres P).word (twWord ((q.1 : ℤ), (q.2 : ℤ)))) :=
    mk_word_tw (finalPres P) ((q.1 : ℤ), (q.2 : ℤ))
  rw [commElt]
  simp only [_root_.map_mul, _root_.map_inv, ht, htw]
  rfl

end Final

end BooneWords
end GroupApproximation
