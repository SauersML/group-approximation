import GroupApproximation.Manuscript.SimpleKazhdanSofic.ContinuedFractionConvergents
import GroupApproximation.Manuscript.SimpleKazhdanSofic.OracleRecursion
import GroupApproximation.Meta.AxiomGuard

/-!
# `α` computes `S`: each digit is one strict comparison

`simple_kazhdan_sofic_group.tex` (origin tip f34e9c0b1), proof of `cor:wp`, second paragraph
(sentence sha256 `a686ac809830`, formerly `7badee43dd9d`):

> Every $D\subseteq\mathbb N$ has the degree of $[0;1+\chi_D(0),1+\chi_D(1),\dots]$, since each
> digit is decided by one strict comparison with a rational computed from earlier digits.

For digits `a_k ∈ {1, 2}` with `k ∈ S ↔ a_k = 2` (the printed `D`) and `α = y_0 = [0; a_0, a_1, …]`
(`ContinuedFractionExpansion.tail`), `charOracle S ≤_T slopeOracle α`, along the printed route:
* the state after `k` steps codes `conv a k = (p_{k-1}, p_k, q_{k-1}, q_k)` and the last digit
  (`stateCode`);
* step `k` asks the one strict comparison `2p_k + p_{k-1} < (2q_k + q_{k-1}) α` (`digitQuery`) and
  sets `a_k = if k % 2 = answer then 2 else 1` (`digitOf_answer`, from `digit_eq_of_answer`);
* after `n + 1` steps the last digit is `a_n`, and `n ∈ S` exactly when it is `2`.
The recursion is `turingReducible_of_oracleRec`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuedFractionOracle

open ContinuedFractionExpansion

/-! ### State codes -/

/-- The code `⟪p_{k-1}, ⟪p_k, ⟪q_{k-1}, ⟪q_k, d⟫⟫⟫⟫` of `(p_{k-1}, p_k, q_{k-1}, q_k)` and a digit `d`. -/
def stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : ℕ :=
  Nat.pair s.1 (Nat.pair s.2.1 (Nat.pair s.2.2.1 (Nat.pair s.2.2.2 d)))

/-- `p_{k-1}` of a state code. -/
def pPrev (i : ℕ) : ℕ := (Nat.unpair i).1

/-- `p_k` of a state code. -/
def pCur (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).2).1

/-- `q_{k-1}` of a state code. -/
def qPrev (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).1

/-- `q_k` of a state code. -/
def qCur (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2).1

/-- The digit of a state code. -/
def lastDigit (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2).2

@[simp] theorem pPrev_stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : pPrev (stateCode s d) = s.1 := by
  simp [pPrev, stateCode]

@[simp] theorem pCur_stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : pCur (stateCode s d) = s.2.1 := by
  simp [pCur, stateCode]

@[simp] theorem qPrev_stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : qPrev (stateCode s d) = s.2.2.1 := by
  simp [qPrev, stateCode]

@[simp] theorem qCur_stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : qCur (stateCode s d) = s.2.2.2 := by
  simp [qCur, stateCode]

@[simp] theorem lastDigit_stateCode (s : ℕ × ℕ × ℕ × ℕ) (d : ℕ) : lastDigit (stateCode s d) = d := by
  simp [lastDigit, stateCode]

theorem primrec_unpair_snd : Primrec fun i : ℕ => (Nat.unpair i).2 :=
  Primrec.snd.comp Primrec.unpair

theorem primrec_pPrev : Primrec pPrev :=
  Primrec.fst.comp Primrec.unpair

theorem primrec_pCur : Primrec pCur :=
  primrec_pPrev.comp primrec_unpair_snd

theorem primrec_qPrev : Primrec qPrev :=
  primrec_pCur.comp primrec_unpair_snd

theorem primrec_qCur : Primrec qCur :=
  primrec_qPrev.comp primrec_unpair_snd

theorem primrec_lastDigit : Primrec lastDigit :=
  primrec_unpair_snd.comp (primrec_unpair_snd.comp (primrec_unpair_snd.comp primrec_unpair_snd))

/-- The state after one more digit `d`: `(p_k, d p_k + p_{k-1}, q_k, d q_k + q_{k-1})`. -/
def advance (i d : ℕ) : ℕ :=
  stateCode (pCur i, d * pCur i + pPrev i, qCur i, d * qCur i + qPrev i) d

theorem advance_stateCode (a : ℕ → ℕ) (k d : ℕ) :
    advance (stateCode (conv a k) d) (a k) = stateCode (conv a (k + 1)) (a k) := by
  rw [advance, pCur_stateCode, pPrev_stateCode, qCur_stateCode, qPrev_stateCode, conv_succ]

theorem primrec_advance : Primrec₂ advance :=
  (Primrec₂.natPair.comp (primrec_pCur.comp Primrec.fst) (Primrec₂.natPair.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.snd (primrec_pCur.comp Primrec.fst))
      (primrec_pPrev.comp Primrec.fst))
    (Primrec₂.natPair.comp (primrec_qCur.comp Primrec.fst) (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.snd (primrec_qCur.comp Primrec.fst))
        (primrec_qPrev.comp Primrec.fst))
      Primrec.snd)))).of_eq fun _ => rfl

/-! ### The digit recursion -/

/-- The strict comparison of step `k`: `2p_k + p_{k-1} < (2q_k + q_{k-1}) α`, on `n = Nat.pair a b`. -/
def digitQuery (i : ℕ) : ℕ :=
  Nat.pair (2 * pCur i + pPrev i) (2 * qCur i + qPrev i)

theorem primrec_digitQuery : Primrec digitQuery :=
  (Primrec₂.natPair.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_pCur) primrec_pPrev)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_qCur) primrec_qPrev)).of_eq
    fun _ => rfl

/-- The digit read off the answer `o` of step `k`. -/
def digitOf (k o : ℕ) : ℕ :=
  if k % 2 = o then 2 else 1

theorem primrec_digitOf : Primrec₂ digitOf :=
  (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) Primrec.snd)
    (Primrec.const 2) (Primrec.const 1)).of_eq fun _ => rfl

/-- Start from `conv a 0 = (1, 0, 0, 1)`. -/
def digitInit (_n : ℕ) : ℕ :=
  stateCode (1, 0, 0, 1) 0

/-- Step `k` queries `digitQuery` of the current state. -/
def digitQueryAt (_n _k i : ℕ) : ℕ :=
  digitQuery i

/-- Step `k` appends the digit read off the answer. -/
def digitStep (_n k i o : ℕ) : ℕ :=
  advance i (digitOf k o)

/-- `n + 1` steps read `a_0, …, a_n`. -/
def digitLen (n : ℕ) : ℕ :=
  n + 1

/-- `n ∈ S` exactly when the last digit is `2`. -/
def digitOut (_n i : ℕ) : ℕ :=
  if lastDigit i = 2 then 1 else 0

theorem primrec_digitInit : Primrec digitInit :=
  (Primrec.const (stateCode (1, 0, 0, 1) 0)).of_eq fun _ => rfl

theorem primrec_digitQueryAt : Primrec fun p : ℕ × ℕ × ℕ => digitQueryAt p.1 p.2.1 p.2.2 :=
  (primrec_digitQuery.comp (Primrec.snd.comp Primrec.snd)).of_eq fun _ => rfl

theorem primrec_digitStep :
    Primrec fun p : (ℕ × ℕ × ℕ) × ℕ => digitStep p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  (primrec_advance.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (primrec_digitOf.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).of_eq
    fun _ => rfl

theorem primrec_digitLen : Primrec digitLen :=
  Primrec.succ.of_eq fun _ => rfl

theorem primrec_digitOut : Primrec₂ digitOut :=
  (Primrec.ite (Primrec.eq.comp (primrec_lastDigit.comp Primrec.snd) (Primrec.const 2))
    (Primrec.const 1) (Primrec.const 0)).of_eq fun _ => rfl

open Classical in
/-- The answers of `slopeOracle α`. -/
noncomputable def slopeValue (α : ℝ) (n : ℕ) : ℕ :=
  if ((Nat.unpair n).1 : ℝ) < ((Nat.unpair n).2 : ℝ) * α then 1 else 0

theorem slopeOracle_eq (α : ℝ) (n : ℕ) : slopeOracle α n = Part.some (slopeValue α n) :=
  rfl

variable {a : ℕ → ℕ}

/-- **One comparison decides the digit** (`digit_eq_of_answer`). -/
theorem digitOf_answer (ha : ∀ k, a k = 1 ∨ a k = 2) (k d : ℕ) :
    digitOf k (slopeValue (tail a ha 0) (digitQuery (stateCode (conv a k) d))) = a k := by
  rw [digit_eq_of_answer ha k]
  simp only [digitOf, slopeValue, digitQuery, pCur_stateCode, pPrev_stateCode, qCur_stateCode,
    qPrev_stateCode, Nat.unpair_pair]

theorem digitState_exists (ha : ∀ k, a k = 1 ∨ a k = 2) (n : ℕ) :
    ∀ k, ∃ d, oracleRecState (slopeValue (tail a ha 0)) digitInit digitQueryAt digitStep n k =
      stateCode (conv a k) d
  | 0 => ⟨0, rfl⟩
  | k + 1 => by
    obtain ⟨d, hd⟩ := digitState_exists ha n k
    refine ⟨a k, ?_⟩
    rw [oracleRecState_succ, hd]
    show advance (stateCode (conv a k) d)
      (digitOf k (slopeValue (tail a ha 0) (digitQuery (stateCode (conv a k) d)))) = _
    rw [digitOf_answer ha k d, advance_stateCode]

theorem digitState_succ (ha : ∀ k, a k = 1 ∨ a k = 2) (n k : ℕ) :
    oracleRecState (slopeValue (tail a ha 0)) digitInit digitQueryAt digitStep n (k + 1) =
      stateCode (conv a (k + 1)) (a k) := by
  obtain ⟨d, hd⟩ := digitState_exists ha n k
  rw [oracleRecState_succ, hd]
  show advance (stateCode (conv a k) d)
    (digitOf k (slopeValue (tail a ha 0) (digitQuery (stateCode (conv a k) d)))) = _
  rw [digitOf_answer ha k d, advance_stateCode]

/-- **`α` computes `S`**: `charOracle S ≤_T slopeOracle [0; a_0, a_1, …]` when `k ∈ S ↔ a_k = 2`,
by one strict comparison per digit. -/
theorem charOracle_turingReducible_slopeOracle (ha : ∀ k, a k = 1 ∨ a k = 2) {S : Set ℕ}
    (hS : ∀ k, k ∈ S ↔ a k = 2) : TuringReducible (charOracle S) (slopeOracle (tail a ha 0)) := by
  refine turingReducible_of_oracleRec (slopeValue (tail a ha 0)) (slopeOracle_eq _) digitInit
    digitQueryAt digitStep digitLen digitOut primrec_digitInit primrec_digitQueryAt
    primrec_digitStep primrec_digitLen primrec_digitOut fun n => ?_
  rw [digitLen, digitState_succ ha n n]
  simp only [charOracle, digitOut, lastDigit_stateCode]
  by_cases h : n ∈ S
  · rw [if_pos h, if_pos ((hS n).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((hS n).2 h')]

end ContinuedFractionOracle
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.digitOf_answer
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.digitState_succ
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ContinuedFractionOracle.charOracle_turingReducible_slopeOracle
