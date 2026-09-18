import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPick
import GroupApproximation.Meta.AxiomGuard

/-!
# Cyclic Bool sequences with at most two kind changes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-32.

List facts behind `extremalJordanPickRun_loopRun` (`Piece10Live/ExtremalJordanPickRun`): a list
`f` whose cyclic kind changes (the pairs of `f.zip (f.rotate 1)` of different `k`-value, the form
of `ExtremalJordanPickChanges`) number at most `2` is one contiguous run up to rotation:
`f = P ++ Q ++ R` with `P ++ R` of one value and `Q` of the other
(`extremalJordanPickRun_runs`).  Deleted wildcard entries are put back by splitting a filter
(`extremalJordanPickRun_lift`).

## Proof

For `f = a :: t` the cyclic pairs are the consecutive pairs of `a :: t ++ [a]`.  Walking along
`t` from `a`: the first change is to the other value, the second change (if any) back to the
value of `a`, and a third change would exceed the bound; the closing entry `a` forces the last
run to have the value of `a` (`extremalJordanPickRun_count_zero`, `_count_one`, `_count_two`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

section PickRunBool

/-- **Two different Bool values**: one is the negation of the other. -/
theorem extremalJordanPickRun_bool_ne {b c : Bool} (h : b ≠ c) : b = !c := by
  revert h
  cases b <;> cases c <;> decide

/-- **Two changes of a Bool value return to it.** -/
theorem extremalJordanPickRun_bool_third {b c d : Bool} (h1 : b ≠ c) (h2 : c ≠ d) : b = d := by
  revert h1 h2
  cases b <;> cases c <;> cases d <;> decide

/-- **No change counted**: equal values. -/
theorem extremalJordanPickRun_eq_of_ite {b c : Bool}
    (h : (if (b != c) = true then 1 else 0) = 0) : b = c := by
  revert h
  cases b <;> cases c <;> decide

/-- **Equal values count no change.** -/
theorem extremalJordanPickRun_ite_eq_zero {b c : Bool} (h : b = c) :
    (if (b != c) = true then 1 else 0) = 0 := by
  subst h
  cases b <;> decide

/-- **Different values count one change.** -/
theorem extremalJordanPickRun_ite_eq_one {b c : Bool} (h : b ≠ c) :
    (if (b != c) = true then 1 else 0) = 1 := by
  revert h
  cases b <;> cases c <;> decide

/-- **A wildcard entry**: `(b || !decide p) = false` gives `b = false` and `p`.  The decidability
instance is implicit, so it is read off the hypothesis. -/
theorem extremalJordanPickRun_wild {b : Bool} {p : Prop} {inst : Decidable p}
    (h : (b || !decide p) = false) : b = false ∧ p := by
  rw [Bool.or_eq_false_iff] at h
  refine ⟨h.1, ?_⟩
  have h2 : decide p = true := by
    have h3 := h.2
    revert h3
    cases decide p <;> decide
  exact of_decide_eq_true h2

end PickRunBool

section PickRunLists

variable {α : Type*} (k : α → Bool)

/-- **Kind changes of `x :: l` closed by `a`**: the consecutive pairs of `x :: l ++ [a]` of
different `k`-value, in the zip form of `ExtremalJordanPickChanges`. -/
def extremalJordanPickRun_count (a x : α) (l : List α) : ℕ :=
  ((x :: l).zip (l ++ [a])).countP (fun p => k p.1 != k p.2)

/-- **One step of the count.** -/
theorem extremalJordanPickRun_count_cons (a x y : α) (l : List α) :
    extremalJordanPickRun_count k a x (y :: l) =
      extremalJordanPickRun_count k a y l + if (k x != k y) = true then 1 else 0 := by
  unfold extremalJordanPickRun_count
  simp only [List.cons_append, List.zip_cons_cons, List.countP_cons]

/-- **No change**: every entry of `l` has the value of `z`. -/
theorem extremalJordanPickRun_count_zero (a : α) :
    ∀ (l : List α) (z : α), extremalJordanPickRun_count k a z l = 0 → ∀ w ∈ l, k w = k z := by
  intro l
  induction l with
  | nil =>
    intro z _ w hw
    exact absurd hw List.not_mem_nil
  | cons y l ih =>
    intro z h w hw
    rw [extremalJordanPickRun_count_cons] at h
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h
    have hzy : k z = k y := extremalJordanPickRun_eq_of_ite h2
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hzy.symm
    · exact (ih y h1 w hw).trans hzy.symm

/-- **At most one change, starting off the value of `a`**: `l` is a run of the other value
followed by a run of the value of `a`. -/
theorem extremalJordanPickRun_count_one (a : α) :
    ∀ (l : List α) (y : α), extremalJordanPickRun_count k a y l ≤ 1 → k y ≠ k a →
      ∃ Q R : List α, l = Q ++ R ∧ (∀ x ∈ Q, k x = !k a) ∧ ∀ x ∈ R, k x = k a := by
  intro l
  induction l with
  | nil =>
    intro y _ _
    exact ⟨[], [], rfl, fun x hx => absurd hx List.not_mem_nil,
      fun x hx => absurd hx List.not_mem_nil⟩
  | cons z l ih =>
    intro y h hy
    rw [extremalJordanPickRun_count_cons] at h
    by_cases hzy : k y = k z
    · rw [extremalJordanPickRun_ite_eq_zero hzy, Nat.add_zero] at h
      have hz : k z ≠ k a := fun h' => hy (hzy.trans h')
      obtain ⟨Q, R, hl, hQ, hR⟩ := ih z h hz
      refine ⟨z :: Q, R, ?_, ?_, hR⟩
      · simp only [hl, List.cons_append]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact extremalJordanPickRun_bool_ne hz
        · exact hQ x hx
    · rw [extremalJordanPickRun_ite_eq_one hzy] at h
      have h0 : extremalJordanPickRun_count k a z l = 0 := by omega
      have hza : k z = k a := extremalJordanPickRun_bool_third (Ne.symm hzy) hy
      refine ⟨[], z :: l, rfl, fun x hx => absurd hx List.not_mem_nil, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hza
      · exact (extremalJordanPickRun_count_zero k a l z h0 x hx).trans hza

/-- **At most two changes, starting on the value of `a`**: `l` is a run of the value of `a`, a
run of the other value, and a run of the value of `a`. -/
theorem extremalJordanPickRun_count_two (a : α) :
    ∀ (l : List α) (x : α), extremalJordanPickRun_count k a x l ≤ 2 → k x = k a →
      ∃ P Q R : List α, l = P ++ Q ++ R ∧ (∀ y ∈ P, k y = k a) ∧ (∀ y ∈ Q, k y = !k a) ∧
        ∀ y ∈ R, k y = k a := by
  intro l
  induction l with
  | nil =>
    intro x _ _
    exact ⟨[], [], [], rfl, fun y hy => absurd hy List.not_mem_nil,
      fun y hy => absurd hy List.not_mem_nil, fun y hy => absurd hy List.not_mem_nil⟩
  | cons z l ih =>
    intro x h hx
    rw [extremalJordanPickRun_count_cons] at h
    by_cases hxz : k x = k z
    · rw [extremalJordanPickRun_ite_eq_zero hxz, Nat.add_zero] at h
      have hz : k z = k a := hxz.symm.trans hx
      obtain ⟨P, Q, R, hl, hP, hQ, hR⟩ := ih z h hz
      refine ⟨z :: P, Q, R, ?_, ?_, hQ, hR⟩
      · simp only [hl, List.cons_append]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hz
        · exact hP y hy
    · rw [extremalJordanPickRun_ite_eq_one hxz] at h
      have h1 : extremalJordanPickRun_count k a z l ≤ 1 := by omega
      have hz : k z ≠ k a := fun h' => hxz (hx.trans h'.symm)
      obtain ⟨Q, R, hl, hQ, hR⟩ := extremalJordanPickRun_count_one k a l z h1 hz
      refine ⟨[], z :: Q, R, ?_, fun y hy => absurd hy List.not_mem_nil, ?_, hR⟩
      · simp only [hl, List.nil_append, List.cons_append]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact extremalJordanPickRun_bool_ne hz
        · exact hQ y hy

/-- **At most two cyclic changes give one run up to rotation**: `f = P ++ Q ++ R` with `P ++ R`
of one value `v` and `Q` of the other. -/
theorem extremalJordanPickRun_runs (f : List α)
    (h : (f.zip (f.rotate 1)).countP (fun p => k p.1 != k p.2) ≤ 2) :
    ∃ (P Q R : List α) (v : Bool), f = P ++ Q ++ R ∧ (∀ x ∈ P ++ R, k x = v) ∧
      ∀ x ∈ Q, k x = !v := by
  cases f with
  | nil =>
    exact ⟨[], [], [], true, rfl, fun x hx => by simp at hx, fun x hx => by simp at hx⟩
  | cons a t =>
    have hrot : (a :: t).rotate 1 = t ++ [a] := by
      have h' := List.rotate_cons_succ t a 0
      rw [List.rotate_zero] at h'
      exact h'
    rw [hrot] at h
    obtain ⟨P, Q, R, ht, hP, hQ, hR⟩ := extremalJordanPickRun_count_two k a t a h rfl
    refine ⟨a :: P, Q, R, k a, ?_, ?_, hQ⟩
    · simp only [ht, List.cons_append]
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact hP x hx
      · exact hR x hx

/-- **Lifting a three-part split of a filter** to a three-part split of the list. -/
theorem extremalJordanPickRun_lift {q : α → Bool} {c P Q R : List α}
    (h : c.filter q = P ++ Q ++ R) :
    ∃ A B C : List α, c = A ++ B ++ C ∧ A.filter q = P ∧ B.filter q = Q ∧ C.filter q = R := by
  obtain ⟨l₁, C, hc, h1, hC⟩ := List.filter_eq_append_iff.mp h
  obtain ⟨A, B, hl, hA, hB⟩ := List.filter_eq_append_iff.mp h1
  exact ⟨A, B, C, by rw [hc, hl], hA, hB, hC⟩

/-- **One run up to wildcards**: if the entries deleted by `q` have `k`-value `false` and
property `L`, and the filtered list has at most two cyclic changes, then `c = A ++ B ++ C` with
`B` false and `A ++ C` true or `L`, or with `A ++ C` false and `B` true or `L`. -/
theorem extremalJordanPickRun_loopRun_list (q : α → Bool) (L : α → Prop) (c : List α)
    (hq : ∀ x, q x = false → k x = false ∧ L x)
    (h : ((c.filter q).zip ((c.filter q).rotate 1)).countP (fun p => k p.1 != k p.2) ≤ 2) :
    ∃ A B C : List α, c = A ++ B ++ C ∧
      (((∀ x ∈ A ++ C, k x = true ∨ L x) ∧ ∀ x ∈ B, k x = false) ∨
        ((∀ x ∈ A ++ C, k x = false) ∧ ∀ x ∈ B, k x = true ∨ L x)) := by
  obtain ⟨P, Q, R, v, hf, hPR, hQ⟩ := extremalJordanPickRun_runs k (c.filter q) h
  obtain ⟨A, B, C, hc, hA, hB, hC⟩ := extremalJordanPickRun_lift hf
  have key : ∀ {Y Z : List α}, Y.filter q = Z → ∀ x ∈ Y, q x = true → x ∈ Z := by
    intro Y Z hY x hx hqx
    rw [← hY]
    exact List.mem_filter.mpr ⟨hx, hqx⟩
  have hAC : ∀ x ∈ A ++ C, q x = true → k x = v := by
    intro x hx hqx
    rcases List.mem_append.mp hx with hx | hx
    · exact hPR x (List.mem_append_left R (key hA x hx hqx))
    · exact hPR x (List.mem_append_right P (key hC x hx hqx))
  have hB' : ∀ x ∈ B, q x = true → k x = !v := fun x hx hqx => hQ x (key hB x hx hqx)
  refine ⟨A, B, C, hc, ?_⟩
  cases v with
  | true =>
    refine Or.inl ⟨fun x hx => ?_, fun x hx => ?_⟩
    · cases hqx : q x with
      | true => exact Or.inl (hAC x hx hqx)
      | false => exact Or.inr (hq x hqx).2
    · cases hqx : q x with
      | true => exact hB' x hx hqx
      | false => exact (hq x hqx).1
  | false =>
    refine Or.inr ⟨fun x hx => ?_, fun x hx => ?_⟩
    · cases hqx : q x with
      | true => exact hAC x hx hqx
      | false => exact (hq x hqx).1
    · cases hqx : q x with
      | true => exact Or.inl (hB' x hx hqx)
      | false => exact Or.inr (hq x hqx).2

end PickRunLists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_bool_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_bool_third
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_eq_of_ite
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_ite_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_ite_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_wild
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_count
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_count_cons
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_count_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_count_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_count_two
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_runs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_lift
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickRun_loopRun_list
