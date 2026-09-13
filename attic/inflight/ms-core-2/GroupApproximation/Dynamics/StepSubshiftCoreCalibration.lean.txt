import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Tactic.FinCases
import GroupApproximation.Dynamics.CoreSubshift
import GroupApproximation.Dynamics.NoncyclicEdgeDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# Calibration of the symbolic core on the step subshift

`non_mf_groups_exist.tex`, proof of Lemma `lem:chain-core-models` (tex lines 1380–1426).

This is a model test, not a carrier.  It runs the landed word-graph definitions of the subshift case
(`WordGraph.IsCyclicEdge`, `WordGraph.CycleCondition`, `ChainCore.coreSubshift`,
`ChainCore.reachableCylinderUnion`) on the smallest system whose chain-recurrent set is proper: the
configurations over `Bool` that switch from `false` to `true` at most once.  The shift on this subshift is
the shift on the two-ended compactification `ℤ ∪ {−∞, +∞}` of tex lines 1769–1772.

The model settles that the definitions are not vacuous at the boundary where the printed argument acts:
* the edge `false → true` of the level-1 word graph is not cyclic, so the subshift fails the cycle condition;
* the symbolic core is exactly the two constant configurations, the fixed points of the shift, as the
  printed characterization of `Y_0` (tex line 1412) predicts;
* the landed defect theorem `shift_mem_diff_of_not_isCyclicEdge` fires on the step configuration, and the
  cylinder union `P` of the vertices reachable from `true` is `{x | x 0 = true}`.
-/

namespace GroupApproximation.ChainCore.StepSubshiftCoreCalibration

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

/-- The step subshift over `Bool`: the configurations that, once `true`, stay `true`. -/
def stepSubshift : Set (ℤ → Bool) := {x | ∀ i j : ℤ, i ≤ j → x i = true → x j = true}

theorem mapsTo_shift_stepSubshift (n : ℤ) : MapsTo (shift n) stepSubshift stepSubshift := by
  intro x hx
  have hx' : ∀ i j : ℤ, i ≤ j → x i = true → x j = true := hx
  show ∀ i j : ℤ, i ≤ j → shift n x i = true → shift n x j = true
  intro i j hij hi
  simp only [shift_apply] at hi ⊢
  exact hx' (n + i) (n + j) (by omega) hi

/-- The configuration switching from `false` to `true` between positions `0` and `1`. -/
def stepPoint : ℤ → Bool := fun i => decide (1 ≤ i)

theorem stepPoint_mem : stepPoint ∈ stepSubshift := by
  show ∀ i j : ℤ, i ≤ j → stepPoint i = true → stepPoint j = true
  intro i j hij hi
  simp only [stepPoint, decide_eq_true_eq] at hi ⊢
  omega

theorem word_stepPoint : word stepPoint 0 (1 + 1) = ![false, true] := by
  funext j
  fin_cases j <;> decide +kernel

theorem false_true_mem_language : ![false, true] ∈ language stepSubshift (1 + 1) :=
  ⟨stepPoint, stepPoint_mem, word_stepPoint⟩

/-- An edge of the level-1 word graph of the step subshift leaving a `true` vertex ends at a `true`
vertex. -/
theorem wordEdge_true {u v : Fin 1 → Bool} (h : wordEdge stepSubshift 1 u v) (hu : u 0 = true) :
    v 0 = true := by
  obtain ⟨w, ⟨x, hx, rfl⟩, rfl, rfl⟩ := h
  have hx' : ∀ i j : ℤ, i ≤ j → x i = true → x j = true := hx
  rw [init_word] at hu
  rw [tail_word]
  simp only [word_apply] at hu ⊢
  exact hx' _ _ (by omega) hu

/-- The `true` vertices of the level-1 word graph are closed under directed paths. -/
theorem reflTransGen_true {u v : Fin 1 → Bool}
    (h : Relation.ReflTransGen (wordEdge stepSubshift 1) u v) (hu : u 0 = true) : v 0 = true := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact wordEdge_true hbc ih

/-- Calibration: the edge `false → true` of the step subshift is not cyclic. -/
theorem not_isCyclicEdge_false_true : ¬ IsCyclicEdge stepSubshift 1 ![false, true] := by
  rintro ⟨-, h⟩
  exact absurd (reflTransGen_true h (by decide +kernel)) (by decide +kernel)

/-- Calibration: the step subshift fails the cycle condition. -/
theorem not_cycleCondition_stepSubshift : ¬ CycleCondition stepSubshift := fun h =>
  not_isCyclicEdge_false_true (h 1 _ false_true_mem_language)

theorem const_mem_stepSubshift (b : Bool) : (fun _ : ℤ => b) ∈ stepSubshift := by
  show ∀ i j : ℤ, i ≤ j → b = true → b = true
  exact fun _ _ _ hb => hb

/-- Calibration: both constant configurations lie in the symbolic core. -/
theorem const_mem_coreSubshift (b : Bool) : (fun _ : ℤ => b) ∈ coreSubshift stepSubshift := by
  rw [mem_coreSubshift_iff]
  intro r i
  refine ⟨word_mem_language mapsTo_shift_stepSubshift (const_mem_stepSubshift b) i (r + 1), ?_⟩
  rw [tail_word, init_word]
  exact Relation.ReflTransGen.refl

/-- Calibration: the step configuration is not in the symbolic core. -/
theorem stepPoint_not_mem_coreSubshift : stepPoint ∉ coreSubshift stepSubshift := by
  intro h
  have h1 := (mem_coreSubshift_iff.1 h) 1 0
  rw [word_stepPoint] at h1
  exact not_isCyclicEdge_false_true h1

/-- A point of the symbolic core stays `true` one step after a `true` coordinate: its level-1 window is a
word of the step subshift. -/
theorem core_step {x : ℤ → Bool} (hx : x ∈ coreSubshift stepSubshift) (i : ℤ) (hi : x i = true) :
    x (i + 1) = true := by
  obtain ⟨⟨y, hy, hyw⟩, -⟩ := (mem_coreSubshift_iff.1 hx) 1 i
  have hy' : ∀ i j : ℤ, i ≤ j → y i = true → y j = true := hy
  have h0 : y 0 = x i := by simpa using congrFun hyw 0
  have h1 : y 1 = x (i + 1) := by simpa using congrFun hyw 1
  rw [← h1]
  exact hy' 0 1 zero_le_one (h0.trans hi)

theorem core_mono {x : ℤ → Bool} (hx : x ∈ coreSubshift stepSubshift) {i : ℤ} (hi : x i = true) :
    ∀ n : ℕ, x (i + n) = true := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, add_zero]; exact hi
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc]
    exact core_step hx _ ih

/-- Calibration: the symbolic core of the step subshift is the pair of constant configurations, the two
fixed points of the shift. -/
theorem coreSubshift_stepSubshift :
    coreSubshift stepSubshift = {fun _ => false, fun _ => true} := by
  ext x
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hx
    have hX : ∀ i j : ℤ, i ≤ j → x i = true → x j = true := by
      intro i j hij hi
      have h := core_mono hx hi (j - i).toNat
      have e : i + ((j - i).toNat : ℤ) = j := by omega
      rwa [e] at h
    by_cases hall : ∀ z : ℤ, x z = true
    · exact Or.inr (funext hall)
    · obtain ⟨z0, hz0⟩ : ∃ z : ℤ, ¬ x z = true := by
        by_contra hne
        exact hall fun z => by
          by_contra hz
          exact hne ⟨z, hz⟩
      by_cases hT : ∃ z : ℤ, x z = true
      · exfalso
        have hB : ∃ b : ℤ, ∀ z : ℤ, x z = true → b ≤ z := by
          refine ⟨z0, fun z hz => ?_⟩
          by_contra hlt
          exact hz0 (hX z z0 (by omega) hz)
        obtain ⟨lb, hlb, hmin⟩ := Int.exists_least_of_bdd hB hT
        have hprev : x (lb - 1) = false := by
          cases hc : x (lb - 1) with
          | false => rfl
          | true => exact absurd (hmin _ hc) (by omega)
        obtain ⟨-, h1⟩ := (mem_coreSubshift_iff.1 hx) 1 (lb - 1)
        rw [tail_word, init_word] at h1
        have h2 := reflTransGen_true h1 (by simpa using hlb)
        have h3 : x (lb - 1) = true := by simpa using h2
        rw [hprev] at h3
        exact absurd h3 (by decide)
      · refine Or.inl (funext fun z => ?_)
        cases hc : x z with
        | false => rfl
        | true => exact (hT ⟨z, hc⟩).elim
  · rintro (rfl | rfl)
    · exact const_mem_coreSubshift false
    · exact const_mem_coreSubshift true

/-- Calibration of `shift_mem_diff_of_not_isCyclicEdge`: the shifted step configuration lies in
`P ∖ T(P)` for the cylinder union `P` of the vertices reachable from the target of the edge `false → true`. -/
theorem shift_stepPoint_mem_defect :
    shift 1 stepPoint ∈ reachableCylinderUnion stepSubshift 1 (Fin.tail ![false, true]) \
      shift 1 '' reachableCylinderUnion stepSubshift 1 (Fin.tail ![false, true]) :=
  shift_mem_diff_of_not_isCyclicEdge mapsTo_shift_stepSubshift false_true_mem_language
    not_isCyclicEdge_false_true stepPoint_mem word_stepPoint

/-- Calibration: the cylinder union of the vertices reachable from `true` is `{x | x 0 = true}`. -/
theorem reachableCylinderUnion_true :
    reachableCylinderUnion stepSubshift 1 ![true] = {x | x ∈ stepSubshift ∧ x 0 = true} := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa using reflTransGen_true h (by decide +kernel)⟩
  · rintro ⟨hx, h0⟩
    refine ⟨hx, ?_⟩
    have hw : word x 0 1 = ![true] := by
      funext j
      fin_cases j
      simpa using h0
    exact (congrArg (Relation.ReflTransGen (wordEdge stepSubshift 1) ![true]) hw).mpr
      Relation.ReflTransGen.refl

end GroupApproximation.ChainCore.StepSubshiftCoreCalibration

#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.core_mono
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.not_isCyclicEdge_false_true
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.not_cycleCondition_stepSubshift
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.const_mem_coreSubshift
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.stepPoint_not_mem_coreSubshift
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.coreSubshift_stepSubshift
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.shift_stepPoint_mem_defect
#audit_axioms GroupApproximation.ChainCore.StepSubshiftCoreCalibration.reachableCylinderUnion_true
