import GroupApproximation.Higman.HigmanPrimitiveRecursiveGraphs

/-!
# Uniqueness of the primitive-recursion run

The transition construction is relational, while a primitive-recursive graph
is functional.  The exact step classifier in
`HigmanPrimitiveRecursiveGraphs` lets us bridge that gap: every accepted run
has the value obtained by iterating the displayed step function.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- The natural value computed after `y` recursion steps, retaining the
integer-valued parameter family used by `recRun`. -/
def iteratedNatRecValue {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (H : List.Vector ℕ (n + 2) → ℕ) (x : ℕ → ℤ) : ℕ → ℕ
  | 0 => F (List.Vector.ofFn fun i : Fin n => (x i.val).toNat)
  | k + 1 => H (natRecArgs (n := n) x (k : ℤ)
      (iteratedNatRecValue F H x k : ℤ))

/-- **A relational run has the unique recursive value.**  This is the forward
semantic half of `natRecGraph_eq`: no matter which witness function `recRun`
supplies, its endpoint after `y` steps is `iteratedNatRecValue F H x y`. -/
theorem recRun_iteratedNatRecValue {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ)
    (x : ℕ → ℤ) (y : ℕ) (z : ℤ)
    (h : recRun n (natGraph F) (natRecStep H) x (y : ℤ) z) :
    z = (iteratedNatRecValue F H x y : ℤ) := by
  rcases h with ⟨-, v, hbase, hstep, hend⟩
  have hbase' := (recBaseAt_natGraph_iff F x (v 0)).mp hbase
  have hv : ∀ k : ℕ, k ≤ y →
      v (k : ℤ) = (iteratedNatRecValue F H x k : ℤ) := by
    intro k hk
    induction k with
    | zero =>
        change v (0 : ℤ) =
          (F (List.Vector.ofFn fun i : Fin n => (x i.val).toNat) : ℤ)
        exact hbase'.2
    | succ k ih =>
        have hklt : (k : ℤ) < (y : ℤ) := by
          exact_mod_cast (Nat.lt_of_succ_le hk)
        have hs := hstep (k : ℤ) (by omega) hklt
        have hclass := (recStepAt_natRecStep_iff H x (k : ℤ)
          (v (k : ℤ)) (v ((k : ℤ) + 1))).mp hs
        have ih' := ih (by omega)
        have hout := hclass.2.2.2
        rw [ih'] at hout
        simpa only [iteratedNatRecValue, Int.toNat_natCast, Nat.cast_add,
          Nat.cast_one] using hout
  exact hend.symm.trans (hv y le_rfl)

/-- The canonical recursive values form a witness for the relational run. -/
theorem recRun_iteratedNatRecValue_exists {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ)
    (x : ℕ → ℤ) (y : ℕ)
    (hx : ∀ j : ℕ, j < n → 0 ≤ x j) :
    recRun n (natGraph F) (natRecStep H) x (y : ℤ)
      (iteratedNatRecValue F H x y : ℤ) := by
  let v : ℤ → ℤ := fun r =>
    if 0 ≤ r then (iteratedNatRecValue F H x r.toNat : ℤ) else 0
  refine ⟨by omega, v, ?_, ?_, ?_⟩
  · apply (recBaseAt_natGraph_iff F x (v 0)).mpr
    refine ⟨hx, ?_⟩
    simp [v, iteratedNatRecValue]
  · intro i hi _
    have hi1 : 0 ≤ i + 1 := by omega
    have htoNat : (i + 1).toNat = i.toNat + 1 := by omega
    apply (recStepAt_natRecStep_iff H x i (v i) (v (i + 1))).mpr
    refine ⟨hx, hi, ?_, ?_⟩
    · simp [v, hi]
    · simp only [v, if_pos hi, if_pos hi1, htoNat, iteratedNatRecValue,
        Int.toNat_of_nonneg hi]
  · simp [v]

/-- Functional form of the exact recursion semantics at a natural step count. -/
theorem recRun_iteratedNatRecValue_iff {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ)
    (x : ℕ → ℤ) (y : ℕ) (z : ℤ)
    (hx : ∀ j : ℕ, j < n → 0 ≤ x j) :
    recRun n (natGraph F) (natRecStep H) x (y : ℤ) z ↔
      z = (iteratedNatRecValue F H x y : ℤ) := by
  constructor
  · exact recRun_iteratedNatRecValue F H x y z
  · rintro rfl
    exact recRun_iteratedNatRecValue_exists F H x y hx

/-! ## From runs to the function graph -/

/-- The recursive value depends on the integer parameters only through their
natural-number values in the first `n` positions. -/
theorem iteratedNatRecValue_congr {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ)
    {x x' : ℕ → ℤ} (hx : ∀ j : ℕ, j < n → (x j).toNat = (x' j).toNat) :
    ∀ y : ℕ, iteratedNatRecValue F H x y = iteratedNatRecValue F H x' y := by
  intro y
  induction y with
  | zero =>
      simp only [iteratedNatRecValue]
      congr 1
      apply List.Vector.eq
      simp [hx]
  | succ k ih =>
      simp only [iteratedNatRecValue]
      congr 1
      rw [ih]
      apply List.Vector.eq
      simp only [natRecArgs]
      simp [hx]

/-- Read the first `n` entries of an `(n+1)`-tuple as integer parameters.
The value outside that range is irrelevant to the recursive evaluator. -/
def natRecParameters {n : ℕ} (a : List.Vector ℕ (n + 1)) (j : ℕ) : ℤ :=
  if hj : j < n then (a.get ⟨j, hj.trans (by omega)⟩ : ℕ) else 0

/-- The ordinary `(n+1)`-ary function computed by the base and step maps. -/
def primitiveRecursionFunction {n : ℕ} (F : List.Vector ℕ n → ℕ)
    (H : List.Vector ℕ (n + 2) → ℕ)
    (a : List.Vector ℕ (n + 1)) : ℕ :=
  iteratedNatRecValue F H (natRecParameters a)
    (a.get ⟨n, by omega⟩)

/-- Evaluating the tuple-level recursion function on integer coordinates is
the same as iterating directly with those integer parameters. -/
theorem primitiveRecursionFunction_ofFn {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ)
    (x : ℕ → ℤ) :
    primitiveRecursionFunction F H
        (List.Vector.ofFn fun i : Fin (n + 1) => (x i.val).toNat) =
      iteratedNatRecValue F H x (x n).toNat := by
  unfold primitiveRecursionFunction
  rw [List.Vector.get_ofFn]
  apply iteratedNatRecValue_congr F H
  intro j hj
  simp only [natRecParameters, dif_pos hj, List.Vector.get_ofFn,
    Int.toNat_natCast]

/-- **Exact graph semantics of the primitive-recursion construction.** -/
theorem natRecGraph_eq_iteratedGraph {n : ℕ}
    (F : List.Vector ℕ n → ℕ) (H : List.Vector ℕ (n + 2) → ℕ) :
    natRecGraph F H = natGraph (primitiveRecursionFunction F H) := by
  ext f
  constructor
  · rintro ⟨hneg, hupper, hrun⟩
    have hwindow : f ∈ windowSupport (n + 2) :=
      (mem_windowSupport_iff (n + 2) f).mpr ⟨hneg, hupper⟩
    rcases hrun with ⟨hy, v, hbase, hstep, hend⟩
    have hparam := (recBaseAt_natGraph_iff F
      (fun j : ℕ => f (j : ℤ)) (v 0)).mp hbase |>.1
    have hrun' : recRun n (natGraph F) (natRecStep H)
        (fun j : ℕ => f (j : ℤ)) ((f (n : ℤ)).toNat : ℤ)
          (f ((n : ℤ) + 1)) := by
      rw [Int.toNat_of_nonneg hy]
      exact ⟨hy, v, hbase, hstep, hend⟩
    have hout := recRun_iteratedNatRecValue F H
      (fun j : ℕ => f (j : ℤ)) (f (n : ℤ)).toNat
      (f ((n : ℤ) + 1)) hrun'
    refine ⟨hwindow, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < n
      · exact hparam i.val hi
      · have hin : i.val = n := by omega
        have hieq : i = ⟨n, by omega⟩ := Fin.ext hin
        rw [hieq]
        simpa using hy
    · calc
        f ((n + 1 : ℕ) : ℤ) =
            iteratedNatRecValue F H (fun j : ℕ => f (j : ℤ))
              (f (n : ℤ)).toNat := by
                simpa only [Nat.cast_add, Nat.cast_one] using hout
        _ = primitiveRecursionFunction F H
            (List.Vector.ofFn fun i : Fin (n + 1) =>
              (f (i.val : ℤ)).toNat) :=
          congrArg (fun q : ℕ => (q : ℤ))
            (primitiveRecursionFunction_ofFn F H
              (fun j : ℕ => f (j : ℤ))).symm
  · rintro ⟨hwindow, hnonneg, hout⟩
    obtain ⟨hneg, hupper⟩ := (mem_windowSupport_iff (n + 2) f).mp hwindow
    have hparam : ∀ j : ℕ, j < n → 0 ≤ f (j : ℤ) := by
      intro j hj
      exact hnonneg ⟨j, by omega⟩
    have hy : 0 ≤ f (n : ℤ) := hnonneg ⟨n, by omega⟩
    have hrun := recRun_iteratedNatRecValue_exists F H
      (fun j : ℕ => f (j : ℤ)) (f (n : ℤ)).toNat hparam
    have hout' : f ((n : ℤ) + 1) =
        (iteratedNatRecValue F H (fun j : ℕ => f (j : ℤ))
          (f (n : ℤ)).toNat : ℤ) := by
      calc
        f ((n : ℤ) + 1) = f ((n + 1 : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_one]
        _ = (primitiveRecursionFunction F H
            (List.Vector.ofFn fun i : Fin (n + 1) =>
              (f (i.val : ℤ)).toNat) : ℤ) := hout
        _ = (iteratedNatRecValue F H (fun j : ℕ => f (j : ℤ))
            (f (n : ℤ)).toNat : ℤ) := by
          exact congrArg (fun q : ℕ => (q : ℤ))
            (primitiveRecursionFunction_ofFn F H
              (fun j : ℕ => f (j : ℤ)))
    refine ⟨hneg, hupper, ?_⟩
    rw [Int.toNat_of_nonneg hy] at hrun
    rw [← hout'] at hrun
    exact hrun

end Seq
end Higman
end GroupApproximation
