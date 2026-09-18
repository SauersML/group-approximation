import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: descents of a cyclic list against a linear order

Lane gl-p07-58.  Pure list combinatorics for the descent-count residual
`FourPieceWitness.WitnessStepDescentStatement`.  Certifies no printed sentence.  NOT COMPILED.

* `witnessStepDescent_pos x L`: the index of the first `x` in `L` (`L.length` if absent).  It is
  defined by recursion, because the dart type carries no `BEq`.
* `witnessStepDescent_steps l := l.zip (l.rotate 1)`: the cyclic steps of `l`.  Every rotation
  step `l.rotate n = s ++ x :: y :: t` gives `(x, y) ∈ steps l` (`witnessStepDescent_mem_steps`).
* `witnessStepDescent_gap f N p`: the forward cyclic gap from `f p.1` to `f p.2` modulo `N`.
  `witnessStepDescent_turn f N p` is `N` at a descent (`¬ f p.1 < f p.2`) and `0` otherwise.
* Telescoping (`witnessStepDescent_gapSum_steps`): over the cyclic steps, the gap sum equals the
  turn sum, i.e. `#descents * N`.
* Counting: one descent gives `N ≤ turnSum`; two distinct descents give `N + N ≤ turnSum`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

section DescentList

variable {α : Type*}

open Classical in
/-- **The index of the first occurrence of `x` in a list** (the length when `x` is absent). -/
noncomputable def witnessStepDescent_pos (x : α) : List α → ℕ
  | [] => 0
  | a :: r => if a = x then 0 else witnessStepDescent_pos x r + 1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos

open Classical in
/-- Unfolding `witnessStepDescent_pos` at a cons. -/
theorem witnessStepDescent_pos_cons (x a : α) (r : List α) :
    witnessStepDescent_pos x (a :: r) =
      if a = x then 0 else witnessStepDescent_pos x r + 1 := rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_cons

open Classical in
/-- The first index of `x` at a list starting with `x` is `0`. -/
theorem witnessStepDescent_pos_cons_self (x : α) (r : List α) :
    witnessStepDescent_pos x (x :: r) = 0 := by
  rw [witnessStepDescent_pos_cons, if_pos rfl]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_cons_self

open Classical in
/-- The first index is at most the length. -/
theorem witnessStepDescent_pos_le_length (x : α) (L : List α) :
    witnessStepDescent_pos x L ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons a r ih =>
    rw [witnessStepDescent_pos_cons, List.length_cons]
    by_cases ha : a = x
    · rw [if_pos ha]
      omega
    · rw [if_neg ha]
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_le_length

open Classical in
/-- Past a prefix avoiding `x`, the first index of `x` shifts by the prefix length. -/
theorem witnessStepDescent_pos_append_of_not_mem {x : α} (r : List α) (pre : List α)
    (h : x ∉ pre) :
    witnessStepDescent_pos x (pre ++ r) = pre.length + witnessStepDescent_pos x r := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : ¬ a = x := fun hax => h (by rw [hax]; exact List.mem_cons_self)
    have hp : x ∉ pre := fun hx => h (List.mem_cons_of_mem a hx)
    rw [List.cons_append, witnessStepDescent_pos_cons, if_neg ha, ih hp, List.length_cons]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_append_of_not_mem

/-- A prefix avoiding `x` lies before the first index of `x`. -/
theorem witnessStepDescent_length_le_pos {x : α} {pre r : List α} (h : x ∉ pre) :
    pre.length ≤ witnessStepDescent_pos x (pre ++ r) := by
  rw [witnessStepDescent_pos_append_of_not_mem r pre h]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_length_le_pos

open Classical in
/-- A dart of the prefix has its first index inside the prefix. -/
theorem witnessStepDescent_pos_lt_of_mem {x : α} (r : List α) (pre : List α) (h : x ∈ pre) :
    witnessStepDescent_pos x (pre ++ r) < pre.length := by
  induction pre with
  | nil => exact absurd h List.not_mem_nil
  | cons a pre ih =>
    rw [List.cons_append, witnessStepDescent_pos_cons, List.length_cons]
    by_cases ha : a = x
    · rw [if_pos ha]
      omega
    · rw [if_neg ha]
      have hx : x ∈ pre := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm ha
        · exact h'
      have := ih hx
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_lt_of_mem

/-- The first index of `y` in `pre ++ y :: z`, when `y ∉ pre`, is `pre.length`. -/
theorem witnessStepDescent_pos_split {y : α} {pre z : List α} (h : y ∉ pre) :
    witnessStepDescent_pos y (pre ++ y :: z) = pre.length := by
  rw [witnessStepDescent_pos_append_of_not_mem (y :: z) pre h,
    witnessStepDescent_pos_cons_self, Nat.add_zero]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_pos_split

/-- **The cyclic steps of a list**: `(l[k], l[k + 1 mod |l|])`. -/
def witnessStepDescent_steps (l : List α) : List (α × α) :=
  l.zip (l.rotate 1)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_steps

/-- **Every rotation step is a cyclic step.** -/
theorem witnessStepDescent_mem_steps {l s t : List α} {n : ℕ} {x y : α}
    (h : l.rotate n = s ++ x :: y :: t) : (x, y) ∈ witnessStepDescent_steps l := by
  have hL : l.rotate (n + s.length) = (x :: y :: t) ++ s := by
    rw [← List.rotate_rotate l n s.length, h, List.rotate_append_length_eq]
  have hrot : (l.rotate 1).rotate (n + s.length) = (l.rotate (n + s.length)).rotate 1 := by
    rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm 1]
  have hz : (witnessStepDescent_steps l).rotate (n + s.length) =
      List.zip ((x :: y :: t) ++ s) (((x :: y :: t) ++ s).rotate 1) := by
    simp only [witnessStepDescent_steps, List.zip_eq_zipWith]
    rw [List.zipWith_rotate_distrib _ _ _ _ (List.length_rotate l 1).symm, hrot, hL]
  have hmem : (x, y) ∈ List.zip ((x :: y :: t) ++ s) (((x :: y :: t) ++ s).rotate 1) := by
    rw [List.cons_append, List.cons_append, List.zip_eq_zipWith, List.zipWith_rotate_one]
    exact List.mem_cons_self
  rw [← hz] at hmem
  exact List.mem_rotate.mp hmem

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_mem_steps

/-- **The forward cyclic gap** from `f p.1` to `f p.2`, modulo `N`. -/
def witnessStepDescent_gap (f : α → ℕ) (N : ℕ) (p : α × α) : ℕ :=
  if f p.1 < f p.2 then f p.2 - f p.1 else f p.2 + N - f p.1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gap

/-- **The turn of a step**: `N` at a descent (`¬ f p.1 < f p.2`), `0` otherwise. -/
def witnessStepDescent_turn (f : α → ℕ) (N : ℕ) (p : α × α) : ℕ :=
  if f p.1 < f p.2 then 0 else N

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turn

/-- **The total forward gap** of a list of steps. -/
def witnessStepDescent_gapSum (f : α → ℕ) (N : ℕ) : List (α × α) → ℕ
  | [] => 0
  | p :: ps => witnessStepDescent_gap f N p + witnessStepDescent_gapSum f N ps

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gapSum

/-- **The total turn** of a list of steps: `N` times the number of descents. -/
def witnessStepDescent_turnSum (f : α → ℕ) (N : ℕ) : List (α × α) → ℕ
  | [] => 0
  | p :: ps => witnessStepDescent_turn f N p + witnessStepDescent_turnSum f N ps

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum

/-- Unfolding the gap sum at a cons. -/
theorem witnessStepDescent_gapSum_cons (f : α → ℕ) (N : ℕ) (p : α × α) (ps : List (α × α)) :
    witnessStepDescent_gapSum f N (p :: ps) =
      witnessStepDescent_gap f N p + witnessStepDescent_gapSum f N ps := rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gapSum_cons

/-- Unfolding the turn sum at a cons. -/
theorem witnessStepDescent_turnSum_cons (f : α → ℕ) (N : ℕ) (p : α × α) (ps : List (α × α)) :
    witnessStepDescent_turnSum f N (p :: ps) =
      witnessStepDescent_turn f N p + witnessStepDescent_turnSum f N ps := rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum_cons

/-- One step: gap plus start equals end plus turn, when the start is at most `N`. -/
theorem witnessStepDescent_gap_add (f : α → ℕ) (N : ℕ) (p : α × α) (h : f p.1 ≤ N) :
    witnessStepDescent_gap f N p + f p.1 = f p.2 + witnessStepDescent_turn f N p := by
  unfold witnessStepDescent_gap witnessStepDescent_turn
  by_cases hp : f p.1 < f p.2
  · rw [if_pos hp, if_pos hp]
    omega
  · rw [if_neg hp, if_neg hp]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gap_add

/-- **Telescoping, list form**: gap sum plus start sum equals end sum plus turn sum. -/
theorem witnessStepDescent_gapSum_add (f : α → ℕ) (N : ℕ) (ps : List (α × α))
    (h : ∀ p ∈ ps, f p.1 ≤ N) :
    witnessStepDescent_gapSum f N ps + ((ps.map Prod.fst).map f).sum =
      ((ps.map Prod.snd).map f).sum + witnessStepDescent_turnSum f N ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h1 := witnessStepDescent_gap_add f N p (h p List.mem_cons_self)
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    rw [witnessStepDescent_gapSum_cons, witnessStepDescent_turnSum_cons, List.map_cons,
      List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gapSum_add

/-- Over the cyclic steps, the start sum equals the end sum (a rotation is a permutation). -/
theorem witnessStepDescent_steps_sum (f : α → ℕ) (l : List α) :
    (((witnessStepDescent_steps l).map Prod.fst).map f).sum =
      (((witnessStepDescent_steps l).map Prod.snd).map f).sum := by
  unfold witnessStepDescent_steps
  rw [List.map_fst_zip (Nat.le_of_eq (List.length_rotate l 1).symm),
    List.map_snd_zip (Nat.le_of_eq (List.length_rotate l 1))]
  exact ((List.rotate_perm l 1).map f).sum_nat.symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_steps_sum

/-- **Telescoping over a cycle**: the forward gap sum of the cyclic steps is the turn sum. -/
theorem witnessStepDescent_gapSum_steps (f : α → ℕ) (N : ℕ) (l : List α) (h : ∀ x, f x ≤ N) :
    witnessStepDescent_gapSum f N (witnessStepDescent_steps l) =
      witnessStepDescent_turnSum f N (witnessStepDescent_steps l) := by
  have h1 := witnessStepDescent_gapSum_add f N (witnessStepDescent_steps l) (fun p _ => h p.1)
  have h2 := witnessStepDescent_steps_sum f l
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_gapSum_steps

/-- The turn of a descent is `N`. -/
theorem witnessStepDescent_turn_of_descent {f : α → ℕ} {N : ℕ} {p : α × α}
    (hp : ¬ f p.1 < f p.2) : witnessStepDescent_turn f N p = N :=
  if_neg hp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turn_of_descent

/-- **One descent turns once.** -/
theorem witnessStepDescent_le_turnSum {f : α → ℕ} {N : ℕ} {p : α × α} (hp : ¬ f p.1 < f p.2)
    (ps : List (α × α)) (hmem : p ∈ ps) : N ≤ witnessStepDescent_turnSum f N ps := by
  induction ps with
  | nil => exact absurd hmem List.not_mem_nil
  | cons q ps ih =>
    rw [witnessStepDescent_turnSum_cons]
    rcases List.mem_cons.mp hmem with hpq | hp'
    · have ht : witnessStepDescent_turn f N q = N :=
        witnessStepDescent_turn_of_descent (by rw [← hpq]; exact hp)
      omega
    · have := ih hp'
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_le_turnSum

/-- **Two distinct descents turn twice.** -/
theorem witnessStepDescent_two_le_turnSum {f : α → ℕ} {N : ℕ} {p q : α × α} (hpq : p ≠ q)
    (hp : ¬ f p.1 < f p.2) (hq : ¬ f q.1 < f q.2) (ps : List (α × α)) (hpm : p ∈ ps)
    (hqm : q ∈ ps) : N + N ≤ witnessStepDescent_turnSum f N ps := by
  induction ps with
  | nil => exact absurd hpm List.not_mem_nil
  | cons r ps ih =>
    rw [witnessStepDescent_turnSum_cons]
    rcases List.mem_cons.mp hpm with hpr | hp'
    · rcases List.mem_cons.mp hqm with hqr | hq'
      · exact absurd (hpr.trans hqr.symm) hpq
      · have ht : witnessStepDescent_turn f N r = N :=
          witnessStepDescent_turn_of_descent (by rw [← hpr]; exact hp)
        have := witnessStepDescent_le_turnSum (f := f) (N := N) hq ps hq'
        omega
    · rcases List.mem_cons.mp hqm with hqr | hq'
      · have ht : witnessStepDescent_turn f N r = N :=
          witnessStepDescent_turn_of_descent (by rw [← hqr]; exact hq)
        have := witnessStepDescent_le_turnSum (f := f) (N := N) hp ps hp'
        omega
      · have := ih hp' hq'
        omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_two_le_turnSum

/-- In a duplicate-free `pre ++ y :: (mid ++ x :: post)`, the dart `x` is not in `pre`. -/
theorem witnessStepDescent_not_mem_pre_right {L pre mid post : List α} {x y : α}
    (hL : L.Nodup) (h : L = pre ++ y :: (mid ++ x :: post)) : x ∉ pre := by
  intro hx
  rw [h] at hL
  exact (List.nodup_append.mp hL).2.2 x hx x (by simp) rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_not_mem_pre_right

end DescentList

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
