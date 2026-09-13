import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Windows of a rotated walk

List facts behind `OsinLemma94CaseOneWalkHolds`:
* blocks of a concatenation over `List.range`, and where they sit in it;
* a list cut at four positions and rotated to one of them, with the cuts in either cyclic order;
* sub-arcs of a `CyclicArc`.
-/

namespace GroupApproximation.GGT.VanKampen.CaseOneWalk

open GroupApproximation.GGT.VanKampen.Embedded

variable {α : Type*}

/-! ## Blocks of a concatenation over `List.range` -/

/-- Splitting `List.range (a + b)` splits the concatenation over it. -/
theorem rangeFlatMap_add (f : ℕ → List α) (a b : ℕ) :
    (List.range (a + b)).flatMap f =
      (List.range a).flatMap f ++ (List.range b).flatMap fun x => f (a + x) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

/-- The last block of the concatenation over `List.range (i + 1)`. -/
theorem rangeFlatMap_succ (f : ℕ → List α) (i : ℕ) :
    (List.range (i + 1)).flatMap f = (List.range i).flatMap f ++ f i := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Block `i < n` comes right after the blocks before it. -/
theorem rangeFlatMap_split (f : ℕ → List α) {i n : ℕ} (h : i < n) :
    ∃ rest, (List.range n).flatMap f = (List.range i).flatMap f ++ (f i ++ rest) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
  refine ⟨(List.range e).flatMap fun x => f (i + 1 + x), ?_⟩
  rw [rangeFlatMap_add, rangeFlatMap_succ, List.append_assoc]

/-- Block `i < n` ends inside the concatenation. -/
theorem rangeFlatMap_length_le (f : ℕ → List α) {i n : ℕ} (h : i < n) :
    ((List.range i).flatMap f).length + (f i).length ≤ ((List.range n).flatMap f).length := by
  obtain ⟨rest, hrest⟩ := rangeFlatMap_split f h
  rw [hrest, List.length_append, List.length_append]
  omega

/-- A window of block `i`, read at its position in the concatenation. -/
theorem rangeFlatMap_drop_take (f : ℕ → List α) {i n t m : ℕ} (h : i < n)
    (htm : t + m ≤ (f i).length) :
    (((List.range n).flatMap f).drop (((List.range i).flatMap f).length + t)).take m =
      ((f i).drop t).take m := by
  obtain ⟨rest, hrest⟩ := rangeFlatMap_split f h
  have h1 : ((List.range i).flatMap f).length ≤ ((List.range i).flatMap f).length + t :=
    Nat.le_add_right _ _
  have h2 : t ≤ (f i).length := by omega
  have h3 : m ≤ ((f i).drop t).length := by
    rw [List.length_drop]
    omega
  rw [hrest, List.drop_append, List.drop_of_length_le h1, Nat.add_sub_cancel_left,
    List.nil_append, List.drop_append_of_le_length h2, List.take_append_of_le_length h3]

/-! ## Rotating at four cuts -/

/-- Cutting `l.drop i` at position `j`. -/
theorem drop_eq_window_append_drop (l : List α) {i j : ℕ} (hij : i ≤ j) :
    l.drop i = (l.drop i).take (j - i) ++ l.drop j := by
  have h := List.take_append_drop (j - i) (l.drop i)
  rw [List.drop_drop, Nat.add_sub_of_le hij] at h
  exact h.symm

/-- Cutting `l.take j` at position `i`. -/
theorem take_eq_take_append_window (l : List α) {i j : ℕ} (hij : i ≤ j) :
    l.take j = l.take i ++ (l.drop i).take (j - i) := by
  rw [← List.take_add, Nat.add_sub_of_le hij]

/-- Rotating to the end `pa'` of a window `[pa, pa']` that comes before a window `[pb', pb]`:
the rotation reads the stretch up to `pb'`, the second window, the stretch around the end back to
`pa`, and the first window. -/
theorem rotate_four_inside (l : List α) {pa pa' pb' pb : ℕ} (h1 : pa ≤ pa') (h2 : pa' ≤ pb')
    (h3 : pb' ≤ pb) (h4 : pb ≤ l.length) :
    l.rotate pa' = (l.drop pa').take (pb' - pa') ++ (l.drop pb').take (pb - pb') ++
      (l.drop pb ++ l.take pa) ++ (l.drop pa).take (pa' - pa) := by
  have h5 : pa' ≤ l.length := by omega
  rw [List.rotate_eq_drop_append_take h5]
  conv_lhs =>
    rw [drop_eq_window_append_drop l h2, drop_eq_window_append_drop l h3,
      take_eq_take_append_window l h1]
  simp only [List.append_assoc]

/-- Rotating to the end `pa'` of a window `[pa, pa']` that comes after a window `[pb', pb]`:
the rotation reads the stretch around the end up to `pb'`, the second window, the stretch up to
`pa`, and the first window. -/
theorem rotate_four_wrap (l : List α) {pb' pb pa pa' : ℕ} (h1 : pb' ≤ pb) (h2 : pb ≤ pa)
    (h3 : pa ≤ pa') (h4 : pa' ≤ l.length) :
    l.rotate pa' = (l.drop pa' ++ l.take pb') ++ (l.drop pb').take (pb - pb') ++
      (l.drop pb).take (pa - pb) ++ (l.drop pa).take (pa' - pa) := by
  rw [List.rotate_eq_drop_append_take h4]
  conv_lhs =>
    rw [take_eq_take_append_window l h3, take_eq_take_append_window l h2,
      take_eq_take_append_window l h1]
  simp only [List.append_assoc]

/-! ## Sub-arcs -/

/-- The darts of an arc, read on the rotated cycle. -/
theorem cyclicArc_darts_eq {cycle : List α} (arc : CyclicArc cycle) :
    arc.darts = (cycle.rotate arc.start.1).take arc.length :=
  congrArg (List.take arc.length) arc.rotated_eq_rotate

/-- The `m` darts of an arc after its first `d` form an arc of the same cycle.  It starts `d`
past the start of the arc unless that passes the end of the cycle. -/
theorem cyclicArc_exists_sub {cycle : List α} (arc : CyclicArc cycle) (d m : ℕ)
    (h : d + m ≤ arc.length) :
    ∃ arc' : CyclicArc cycle, arc'.length = m ∧ arc'.darts = (arc.darts.drop d).take m ∧
      (arc.start.1 + d < cycle.length → arc'.start.1 = arc.start.1 + d) := by
  have hlen := arc.length_le
  have hst := arc.start.2
  have hmod : (arc.start.1 + d) % cycle.length ≤ arc.start.1 + d := Nat.mod_le _ _
  have hbound : (arc.start.1 + d) % cycle.length < cycle.length + 1 := by
    rcases Nat.eq_zero_or_pos cycle.length with h0 | hpos
    · exact Nat.lt_succ_of_le (le_trans hmod (by omega))
    · exact Nat.lt_succ_of_lt (Nat.mod_lt _ hpos)
  have hml : m ≤ cycle.length := by omega
  refine ⟨⟨⟨(arc.start.1 + d) % cycle.length, hbound⟩, m, hml⟩, rfl, ?_,
    fun hlt => Nat.mod_eq_of_lt hlt⟩
  have e1 : (⟨⟨(arc.start.1 + d) % cycle.length, hbound⟩, m, hml⟩ : CyclicArc cycle).darts =
      (cycle.rotate ((arc.start.1 + d) % cycle.length)).take m :=
    cyclicArc_darts_eq _
  have hd : d ≤ (cycle.rotate arc.start.1).length := by
    rw [List.length_rotate]
    omega
  have hm : m ≤ ((cycle.rotate arc.start.1).drop d).length := by
    rw [List.length_drop, List.length_rotate]
    omega
  have hm' : m ≤ arc.length - d := by omega
  rw [e1, cyclicArc_darts_eq arc, List.rotate_mod, ← List.rotate_rotate,
    List.rotate_eq_drop_append_take hd, List.take_append_of_le_length hm, List.drop_take,
    List.take_take, Nat.min_eq_left hm']

/-- A window of a reversed list is a reversed window, read from the other end. -/
theorem reverse_window_eq (l : List α) {a m : ℕ} (h : a + m ≤ l.length) :
    (l.reverse.drop a).take m = ((l.drop (l.length - a - m)).take m).reverse := by
  have hmin : min (l.length - a) l.length = l.length - a := by omega
  have hsub : l.length - a - (l.length - a - m) = m := by omega
  rw [List.drop_reverse, List.take_reverse, List.length_take, hmin, List.drop_take, hsub]

#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.cyclicArc_exists_sub
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.rotate_four_wrap

end GroupApproximation.GGT.VanKampen.CaseOneWalk
