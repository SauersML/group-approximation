import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Stages
import GroupApproximation.Meta.AxiomGuard

/-!
# Three-cycles of `Fin 5` as commutators of shifted three-cycles

The step of the word recursion behind `L(X) ≤_T WP` for the derived topological full group
(`SKTFG.LanguageToWordProblem`). A label `i < 125` codes the three-cycle
`cyc (i / 25) (i / 5 % 5) (i % 5)` of `Fin 5`. For a label `i` with three distinct entries,
`pick i` is a pair of such labels `(α, β)` with `⁅α, β⁆ = τ` in `Perm (Fin 6)`, where `α` and `τ`
act on the levels `0, …, 4` and `β` on the levels `1, …, 5` (`pick_spec`). This is
`⁅(x y p), (p u v)⁆ = (x u p)`: rotate `τ = (x u p)` so that `u, p ≠ 0`, take `y` off `x, u, p`,
and `v = 5`.
-/

namespace GroupApproximation.Full.SKTFG

open Equiv
open scoped commutatorElement

/-- The first entry of a label, in base `5`. -/
def lab1 (i : Fin 125) : Fin 5 := ⟨i.val / 25, by have := i.isLt; omega⟩

/-- The second entry of a label. -/
def lab2 (i : Fin 125) : Fin 5 := ⟨i.val / 5 % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The third entry of a label. -/
def lab3 (i : Fin 125) : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The label of `(a, b, c)`. -/
def mkLab (a b c : Fin 5) : Fin 125 :=
  ⟨25 * a.val + 5 * b.val + c.val, by have := a.isLt; have := b.isLt; have := c.isLt; omega⟩

/-- The three-cycle of a label. -/
def labPerm (i : Fin 125) : Perm (Fin 5) := cyc (lab1 i) (lab2 i) (lab3 i)

/-- The three-cycle of a label on the levels `0, …, 4` of `Fin 6`. -/
def labPermC (i : Fin 125) : Perm (Fin 6) :=
  cyc (lab1 i).castSucc (lab2 i).castSucc (lab3 i).castSucc

/-- The three-cycle of a label on the levels `1, …, 5` of `Fin 6`. -/
def labPermS (i : Fin 125) : Perm (Fin 6) := cyc (lab1 i).succ (lab2 i).succ (lab3 i).succ

/-- A label with three distinct entries. -/
abbrev LabValid (i : Fin 125) : Prop := lab1 i ≠ lab2 i ∧ lab1 i ≠ lab3 i ∧ lab2 i ≠ lab3 i

/-- `(a, b, c)` rotated so that its last two entries are not `0`, when they are distinct. -/
def rot (a b c : Fin 5) : Fin 5 × Fin 5 × Fin 5 :=
  if b = 0 then (b, c, a) else if c = 0 then (c, a, b) else (a, b, c)

/-- A point of `Fin 5` other than `x, u, p`. -/
def freePt (x u p : Fin 5) : Fin 5 :=
  ((List.finRange 5).find? fun y => decide (y ≠ x ∧ y ≠ u ∧ y ≠ p)).getD 0

/-- The witnesses `(x y p)` and `(p-1 u-1 4)` for `(x u p)`. -/
def pickOf (r : Fin 5 × Fin 5 × Fin 5) : Fin 125 × Fin 125 :=
  (mkLab r.1 (freePt r.1 r.2.1 r.2.2) r.2.2, mkLab (r.2.2 - 1) (r.2.1 - 1) 4)

/-- The witness pair of a label. -/
def pick (i : Fin 125) : Fin 125 × Fin 125 := pickOf (rot (lab1 i) (lab2 i) (lab3 i))

/-- **The witness table.** -/
theorem pick_spec : ∀ i : Fin 125, LabValid i →
    LabValid (pick i).1 ∧ LabValid (pick i).2 ∧
      ⁅labPermC (pick i).1, labPermS (pick i).2⁆ = labPermC i := by
  decide +kernel

theorem cyc_map {m n : ℕ} {f : Fin m → Fin n} (hf : Function.Injective f) (a b c i : Fin m) :
    cyc (f a) (f b) (f c) (f i) = f (cyc a b c i) := by
  rw [cyc, cyc, Perm.mul_apply, Perm.mul_apply, hf.swap_apply, hf.swap_apply]

theorem cyc_apply_of_ne {n : ℕ} {a b c j : Fin n} (ha : j ≠ a) (hb : j ≠ b) (hc : j ≠ c) :
    cyc a b c j = j := by
  rw [cyc, Perm.mul_apply, swap_apply_of_ne_of_ne ha hb, swap_apply_of_ne_of_ne ha hc]

theorem labPermC_castSucc (i : Fin 125) (j : Fin 5) :
    labPermC i j.castSucc = (labPerm i j).castSucc :=
  cyc_map (Fin.castSucc_injective 5) _ _ _ _

theorem labPermC_last (i : Fin 125) : labPermC i (Fin.last 5) = Fin.last 5 :=
  cyc_apply_of_ne (Fin.castSucc_lt_last _).ne' (Fin.castSucc_lt_last _).ne'
    (Fin.castSucc_lt_last _).ne'

theorem labPermS_succ (i : Fin 125) (j : Fin 5) : labPermS i j.succ = (labPerm i j).succ :=
  cyc_map (Fin.succ_injective 5) _ _ _ _

theorem labPermS_zero (i : Fin 125) : labPermS i 0 = 0 :=
  cyc_apply_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm

theorem labPermC_of_not_castSucc (i : Fin 125) (j : Fin 6) (hj : ∀ k : Fin 5, k.castSucc ≠ j) :
    labPermC i j = j := by
  cases j using Fin.lastCases with
  | last => exact labPermC_last i
  | cast k => exact absurd rfl (hj k)

theorem labPerm_mem_alternatingGroup {i : Fin 125} (h : LabValid i) :
    labPerm i ∈ alternatingGroup (Fin 5) :=
  cyc_mem_alternatingGroup h.1 h.2.1

/-- The root label `(0 1 2)`. -/
def rootLab : Fin 125 := mkLab 0 1 2

theorem rootLab_valid : LabValid rootLab := by decide

theorem labPerm_rootLab_zero : labPerm rootLab 0 ≠ 0 := by decide

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.pick_spec
