import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.Macros
import GroupApproximation.Computability.BooneGroupModularMachine
import Mathlib.Tactic.DeriveFintype

/-!
# The structured machine simulating a modular machine

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  For a
modular machine `mm` with modulus `m = mm.size` we build a structured machine
with five glasses: `0 = α`, `1 = β`, `2 = U`, `3 = V`, and `4`, which stays
empty and serves for unconditional jumps.  One modular step goes as follows.

* `divA`, `carA`: divide `α` by `m`; the remainder is stored in the state and the
  quotient goes to `U`.
* `divB`, `carB`: do the same for `β`, with quotient in `V`.
* `disp a b`: look up the quadruple for the digits `(a, b)`.
* `R` quadruple `(a, b, c, R)`: `mulR`, `addR` set `α := U·m²`, `plusR` adds
  `c`, and `trR`, `trR'` move `V` into `β`.
* `L` quadruple: `trL`, `trL'` move `U` into `α`, `mulL`, `addL` set
  `β := V·m²`, and `plusL` adds `c`.
* No quadruple: the machine stops if `U = V = 0` and the digits are `0`, and is
  stuck otherwise.

Digits, counters and written values are all at most `m²`, so the states use
`Fin (m² + 1)`.
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

open GroupApproximation.BooneGroup

/-- The states of the simulating machine (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
inductive St (B : ℕ) : Type where
  | stop
  | stuck
  | divA (r : Fin (B + 1))
  | carA
  | divB (a r : Fin (B + 1))
  | carB (a : Fin (B + 1))
  | disp (a b : Fin (B + 1))
  | chk0
  | mulR (c : Fin (B + 1))
  | addR (c k : Fin (B + 1))
  | plusR (k : Fin (B + 1))
  | trR
  | trR'
  | trL (c : Fin (B + 1))
  | trL' (c : Fin (B + 1))
  | mulL (c : Fin (B + 1))
  | addL (c k : Fin (B + 1))
  | plusL (k : Fin (B + 1))
  deriving Fintype

variable (mm : ModularMachine)

/-- A number as a state index (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
def ix (k : ℕ) : Fin (mm.size ^ 2 + 1) :=
  ⟨k % (mm.size ^ 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The value of an index in range (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem val_ix {k : ℕ} (h : k ≤ mm.size ^ 2) : (ix mm k).val = k :=
  Nat.mod_eq_of_lt (by omega)

/-- The modulus is at most its square (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem size_le_sq : mm.size ≤ mm.size ^ 2 := by
  rw [Nat.pow_two]
  exact Nat.le_mul_of_pos_left _ mm.size_pos

/-- The instruction at `disp a b` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
def dispInstr (a b : Fin (mm.size ^ 2 + 1)) : Option (TInstr 5 (St (mm.size ^ 2))) :=
  Option.elim (mm.quad a.val b.val)
    (if a.val = 0 ∧ b.val = 0 then some (TInstr.test 2 St.stuck St.chk0) else none)
    (fun q ↦ some (cond q.2 (TInstr.test 4 (St.mulR (ix mm q.1)) (St.mulR (ix mm q.1)))
      (TInstr.test 4 (St.trL (ix mm q.1)) (St.trL (ix mm q.1)))))

/-- The instruction table of the simulating machine (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def delta : St (mm.size ^ 2) → Option (TInstr 5 (St (mm.size ^ 2)))
  | St.stop => none
  | St.stuck => none
  | St.divA r => some (TInstr.test 0
      (if r.val + 1 < mm.size then St.divA (ix mm (r.val + 1)) else St.carA)
      (St.divB r (ix mm 0)))
  | St.carA => some (TInstr.add 2 (St.divA (ix mm 0)))
  | St.divB a r => some (TInstr.test 1
      (if r.val + 1 < mm.size then St.divB a (ix mm (r.val + 1)) else St.carB a)
      (St.disp a r))
  | St.carB a => some (TInstr.add 3 (St.divB a (ix mm 0)))
  | St.disp a b => dispInstr mm a b
  | St.chk0 => some (TInstr.test 3 St.stuck St.stop)
  | St.mulR c => some (TInstr.test 2 (St.addR c (ix mm (mm.size ^ 2))) (St.plusR c))
  | St.addR c k => if k.val = 0 then some (TInstr.test 4 (St.mulR c) (St.mulR c))
      else some (TInstr.add 0 (St.addR c (ix mm (k.val - 1))))
  | St.plusR k => if k.val = 0 then some (TInstr.test 4 St.trR St.trR)
      else some (TInstr.add 0 (St.plusR (ix mm (k.val - 1))))
  | St.trR => some (TInstr.test 3 St.trR' (St.divA (ix mm 0)))
  | St.trR' => some (TInstr.add 1 St.trR)
  | St.trL c => some (TInstr.test 2 (St.trL' c) (St.mulL c))
  | St.trL' c => some (TInstr.add 0 (St.trL c))
  | St.mulL c => some (TInstr.test 3 (St.addL c (ix mm (mm.size ^ 2))) (St.plusL c))
  | St.addL c k => if k.val = 0 then some (TInstr.test 4 (St.mulL c) (St.mulL c))
      else some (TInstr.add 1 (St.addL c (ix mm (k.val - 1))))
  | St.plusL k => if k.val = 0 then some (TInstr.test 4 (St.divA (ix mm 0)) (St.divA (ix mm 0)))
      else some (TInstr.add 1 (St.plusL (ix mm (k.val - 1))))

/-- The simulating structured machine (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def tm : TMachine 5 (St (mm.size ^ 2)) where
  δ := delta mm
  stop := St.stop
  δ_stop := rfl

/-! ## The instruction table on indexed states -/

theorem delta_divA {r : ℕ} (hr : r < mm.size) :
    (tm mm).δ (St.divA (ix mm r)) = some (TInstr.test 0
      (if r + 1 < mm.size then St.divA (ix mm (r + 1)) else St.carA)
      (St.divB (ix mm r) (ix mm 0))) := by
  have hv : (ix mm r).val = r := val_ix mm (by have := size_le_sq mm; omega)
  have e0 : (tm mm).δ (St.divA (ix mm r)) = some (TInstr.test 0
      (if (ix mm r).val + 1 < mm.size then St.divA (ix mm ((ix mm r).val + 1)) else St.carA)
      (St.divB (ix mm r) (ix mm 0))) := rfl
  rw [hv] at e0
  exact e0

theorem delta_carA : (tm mm).δ St.carA = some (TInstr.add 2 (St.divA (ix mm 0))) := rfl

theorem delta_divB (a : ℕ) {r : ℕ} (hr : r < mm.size) :
    (tm mm).δ (St.divB (ix mm a) (ix mm r)) = some (TInstr.test 1
      (if r + 1 < mm.size then St.divB (ix mm a) (ix mm (r + 1)) else St.carB (ix mm a))
      (St.disp (ix mm a) (ix mm r))) := by
  have hv : (ix mm r).val = r := val_ix mm (by have := size_le_sq mm; omega)
  have e0 : (tm mm).δ (St.divB (ix mm a) (ix mm r)) = some (TInstr.test 1
      (if (ix mm r).val + 1 < mm.size then St.divB (ix mm a) (ix mm ((ix mm r).val + 1))
        else St.carB (ix mm a))
      (St.disp (ix mm a) (ix mm r))) := rfl
  rw [hv] at e0
  exact e0

theorem delta_carB (a : ℕ) :
    (tm mm).δ (St.carB (ix mm a)) = some (TInstr.add 3 (St.divB (ix mm a) (ix mm 0))) := rfl

theorem delta_disp_eq {a b : ℕ} (ha : a < mm.size) (hb : b < mm.size) :
    (tm mm).δ (St.disp (ix mm a) (ix mm b)) = Option.elim (mm.quad a b)
      (if a = 0 ∧ b = 0 then some (TInstr.test 2 St.stuck St.chk0) else none)
      (fun q ↦ some (cond q.2 (TInstr.test 4 (St.mulR (ix mm q.1)) (St.mulR (ix mm q.1)))
        (TInstr.test 4 (St.trL (ix mm q.1)) (St.trL (ix mm q.1))))) := by
  have hva : (ix mm a).val = a := val_ix mm (by have := size_le_sq mm; omega)
  have hvb : (ix mm b).val = b := val_ix mm (by have := size_le_sq mm; omega)
  have e0 : (tm mm).δ (St.disp (ix mm a) (ix mm b)) = dispInstr mm (ix mm a) (ix mm b) := rfl
  rw [dispInstr, hva, hvb] at e0
  exact e0

theorem delta_disp_true {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (h : mm.quad a b = some (c, true)) :
    (tm mm).δ (St.disp (ix mm a) (ix mm b)) =
      some (TInstr.test 4 (St.mulR (ix mm c)) (St.mulR (ix mm c))) := by
  have e0 := delta_disp_eq mm ha hb
  rw [h] at e0
  exact e0

theorem delta_disp_false {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (h : mm.quad a b = some (c, false)) :
    (tm mm).δ (St.disp (ix mm a) (ix mm b)) =
      some (TInstr.test 4 (St.trL (ix mm c)) (St.trL (ix mm c))) := by
  have e0 := delta_disp_eq mm ha hb
  rw [h] at e0
  exact e0

theorem delta_disp_none {a b : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (h : mm.quad a b = none) (hab : ¬ (a = 0 ∧ b = 0)) :
    (tm mm).δ (St.disp (ix mm a) (ix mm b)) = none := by
  have e0 := delta_disp_eq mm ha hb
  rw [h, if_neg hab] at e0
  exact e0

theorem delta_disp_zero :
    (tm mm).δ (St.disp (ix mm 0) (ix mm 0)) = some (TInstr.test 2 St.stuck St.chk0) := by
  have e0 := delta_disp_eq mm mm.size_pos mm.size_pos
  have h00 : (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 := ⟨rfl, rfl⟩
  rw [mm.quad_zero_zero, if_pos h00] at e0
  exact e0

theorem delta_chk0 : (tm mm).δ St.chk0 = some (TInstr.test 3 St.stuck St.stop) := rfl

theorem delta_stuck : (tm mm).δ St.stuck = none := rfl

theorem delta_mulR (c : Fin (mm.size ^ 2 + 1)) :
    (tm mm).δ (St.mulR c) = some (TInstr.test 2 (St.addR c (ix mm (mm.size ^ 2))) (St.plusR c)) :=
  rfl

theorem delta_trR : (tm mm).δ St.trR = some (TInstr.test 3 St.trR' (St.divA (ix mm 0))) := rfl

theorem delta_trR' : (tm mm).δ St.trR' = some (TInstr.add 1 St.trR) := rfl

theorem delta_trL (c : Fin (mm.size ^ 2 + 1)) :
    (tm mm).δ (St.trL c) = some (TInstr.test 2 (St.trL' c) (St.mulL c)) := rfl

theorem delta_trL' (c : Fin (mm.size ^ 2 + 1)) :
    (tm mm).δ (St.trL' c) = some (TInstr.add 0 (St.trL c)) := rfl

theorem delta_mulL (c : Fin (mm.size ^ 2 + 1)) :
    (tm mm).δ (St.mulL c) = some (TInstr.test 3 (St.addL c (ix mm (mm.size ^ 2))) (St.plusL c)) :=
  rfl

end GroupApproximation.Full.Kharlampovich.MinskySim
