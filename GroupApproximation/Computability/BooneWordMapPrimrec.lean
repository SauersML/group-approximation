import GroupApproximation.Computability.BooneWords
import Mathlib.Computability.Primrec.List

/-!
# The halting word is a computable function of the configuration

`BooneWords.rawComm` writes `k⁻¹ · t(α,β) · k · t(α,β)⁻¹` as raw data.  It is a
`noncomputable def`, because the four generator indices it uses are read off a
choice-based enumeration — and that does not matter in the slightest.  For a
fixed presentation the indices are **fixed naturals**, and the word is
`List.replicate` and `List.append` over them, so the map from a configuration to
its word is primitive recursive whether or not those naturals can be evaluated.

This is the same observation that made the machine half of `D4'` tractable: an
object may be noncomputable while the function of the varying argument is
computable.  Trying to make the *object* effective is the wrong obligation.

Mathlib has no `Primrec` fact for `List.replicate`, so `primrec_replicate` is
proved here from `Primrec.nat_rec₁`; everything above it is `list_append`,
`list_map` and `list_reverse`.
-/

namespace GroupApproximation
namespace Computability

open BooneWords PresentationCodes RawWord BooneGroup BooneTowerPresentation

/-- Repetition of a fixed letter is primitive recursive.  Not in Mathlib. -/
theorem primrec_replicate (a : ℕ × Bool) :
    Primrec (fun n : ℕ => List.replicate n a) := by
  have h : Primrec (Nat.rec ([] : List (ℕ × Bool))
      (fun _ ih => a :: ih) : ℕ → List (ℕ × Bool)) :=
    Primrec.nat_rec₁ _ (Primrec.list_cons.comp (Primrec.const a) Primrec.snd).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ← ih]

/-- Inverting a raw word is primitive recursive. -/
theorem primrec_invWord : Primrec invWord := by
  have hmap : Primrec (fun u : List (ℕ × Bool) => u.map fun p => (p.1, !p.2)) :=
    Primrec.list_map Primrec.id
      ((Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂)
  exact Primrec.list_reverse.comp hmap

variable {S : Stage} (P : StagePres S)

/-- The `x^α y^β` half of the word, computably in `(α, β)`. -/
theorem primrec_rawSh : Primrec (rawSh P) := by
  have h1 : Primrec (fun q : ℕ × ℕ => List.replicate q.1 (genIdx P 1, true)) :=
    (primrec_replicate _).comp Primrec.fst
  have h2 : Primrec (fun q : ℕ × ℕ => List.replicate q.2 (genIdx P 2, true)) :=
    (primrec_replicate _).comp Primrec.snd
  exact (Primrec.list_append.comp h1 h2).of_eq fun q => rfl

/-- `t(α,β)`, computably in `(α, β)`. -/
theorem primrec_rawTw : Primrec (rawTw P) := by
  have hinv : Primrec (fun q : ℕ × ℕ => invWord (rawSh P q)) :=
    primrec_invWord.comp (primrec_rawSh P)
  have hcons : Primrec (fun q : ℕ × ℕ => (genIdx P 0, true) :: rawSh P q) :=
    Primrec.list_cons.comp (Primrec.const _) (primrec_rawSh P)
  exact (Primrec.list_append.comp hinv hcons).of_eq fun q => rfl

/-- **The halting word is a computable function of the configuration.** -/
theorem primrec_rawComm : Primrec (rawComm P) := by
  have hinv : Primrec (fun q : ℕ × ℕ => invWord (rawTw (finalPres P) q)) :=
    primrec_invWord.comp (primrec_rawTw (finalPres P))
  have hcons : Primrec (fun q : ℕ × ℕ =>
      (kIdx P, true) :: invWord (rawTw (finalPres P) q)) :=
    Primrec.list_cons.comp (Primrec.const (kIdx P, true)) hinv
  have happ : Primrec (fun q : ℕ × ℕ =>
      rawTw (finalPres P) q ++ (kIdx P, true) :: invWord (rawTw (finalPres P) q)) :=
    Primrec.list_append.comp (primrec_rawTw (finalPres P)) hcons
  refine (Primrec.list_cons.comp (Primrec.const (kIdx P, false)) happ).of_eq fun q => ?_
  show (kIdx P, false) :: (rawTw (finalPres P) q ++
      (kIdx P, true) :: invWord (rawTw (finalPres P) q)) = rawComm P q
  rfl

/-- The same, as `Computable`, which is the form the reduction consumes. -/
theorem computable_rawComm : Computable (rawComm P) :=
  (primrec_rawComm P).to_comp

end Computability
end GroupApproximation
