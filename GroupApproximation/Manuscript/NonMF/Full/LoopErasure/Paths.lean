import GroupApproximation.Dynamics.PartialShiftClasses
import GroupApproximation.Dynamics.TransientClassSaturation
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Erasing loops in paths of partial shifts

`non_mf_groups_exist.tex`, proof of `\label{lem:transient-matrices}` (census row `ff376e50f433`,
recorded at tex l.1489; the sentence is tex l.1504–1505 in the current manuscript):

> The equivalence relation they generate on $C$ has classes of size at most $m$.  Erasing loops
> shortens any path between related points to at most $m-1$ steps.

Setting, as in `Dynamics/PartialShiftClasses`: `T : X ≃ₜ X`, `C ⊆ X`, `E : Finset ℤ` the
exponents of the partial shifts, `stepExponents E = E ∪ -E`, and `ExponentBound T C m` the orbit
bound (each orbit meets `C` in at most `m` points).

* `IsStepPath T C E x l`: the list `l` of steps is a path from `x`.  Every step lies in
  `stepExponents E` and every visited point `T^{(l.take j).sum} x`, `0 ≤ j ≤ l.length`, lies in `C`.
* `mem_reachableExponents_iff_path`: `reachableExponents T C E r x` is exactly the set of
  endpoints of paths of at most `r` steps.
* `isStepPath_eraseSegment`: when two prefix sums agree, deleting the segment between them is a
  shorter path with the same endpoint (loop deletion).
* `length_le_of_injective`: a path without loops has at most `m - 1` steps.  Its `length + 1`
  visited levels are distinct exponents returning `x` to `C` (pigeonhole via `ExponentBound`).
* `exists_short_path_of_path`: **erasing loops**, by strong induction on the length.
* `reachableExponents_subset_of_exponentBound`: the stage form, the exponents reached in `r`
  steps are reached in `m - 1` steps.
* `PrintedErasingLoopsSentence` and its closed proof `printedErasingLoopsSentence`.
-/

namespace GroupApproximation.Full.NM18

open GroupApproximation.ChainCore

universe u

section Paths

variable {X : Type u} [TopologicalSpace X] {T : X ≃ₜ X} {C : Set X} {E : Finset ℤ} {m : ℕ}

/-- A path of partial shifts from `x` (tex 1504–1505): the steps of `l` are partial-shift exponents
or their inverses, and all visited points `T^{(l.take j).sum} x`, `0 ≤ j ≤ l.length`, lie in
`C`. -/
def IsStepPath (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (x : X) (l : List ℤ) : Prop :=
  (∀ j ≤ l.length, (T ^ (l.take j).sum) x ∈ C) ∧ ∀ e ∈ l, e ∈ stepExponents E

/-- The empty path from a point of `C`. -/
theorem isStepPath_nil {x : X} (hx : x ∈ C) : IsStepPath T C E x [] := by
  refine ⟨fun j _ => ?_, fun e he => absurd he List.not_mem_nil⟩
  rw [List.take_nil, List.sum_nil, zpow_zero, Homeomorph.one_apply]
  exact hx

/-- Extending a path by one step. -/
theorem isStepPath_concat {x : X} {l : List ℤ} {e : ℤ} (hl : IsStepPath T C E x l)
    (he : e ∈ stepExponents E) (hC : (T ^ (l.sum + e)) x ∈ C) :
    IsStepPath T C E x (l ++ [e]) := by
  refine ⟨fun j hj => ?_, fun e' he' => ?_⟩
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j ≤ l.length
    · rw [List.take_append_of_le_length hjl]
      exact hl.1 j hjl
    · have hlen : (l ++ [e]).length ≤ j := by
        rw [List.length_append, List.length_singleton]
        omega
      rw [List.take_of_length_le hlen, List.sum_append, List.sum_singleton]
      exact hC
  · rcases List.mem_append.1 he' with h | h
    · exact hl.2 e' h
    · rw [List.mem_singleton] at h
      rw [h]
      exact he

/-- Every exponent reached in `r` steps is the endpoint of a path of at most `r` steps. -/
theorem exists_path_of_mem_reachableExponents {x : X} :
    ∀ (r : ℕ) {d : ℤ}, d ∈ reachableExponents T C E r x →
      ∃ l : List ℤ, l.length ≤ r ∧ IsStepPath T C E x l ∧ l.sum = d := by
  intro r
  induction r with
  | zero =>
    intro d hd
    obtain ⟨rfl, hx⟩ := mem_reachableExponents_zero.1 hd
    exact ⟨[], Nat.le_refl 0, isStepPath_nil hx, List.sum_nil⟩
  | succ r ih =>
    intro d hd
    obtain ⟨hcase, hdC⟩ := mem_reachableExponents_succ.1 hd
    rcases hcase with hd' | ⟨a, ha, e, he, hae⟩
    · obtain ⟨l, hlen, hl, hsum⟩ := ih hd'
      exact ⟨l, by omega, hl, hsum⟩
    · obtain ⟨l, hlen, hl, hsum⟩ := ih ha
      have hC : (T ^ (l.sum + e)) x ∈ C := by
        rw [hsum, hae]
        exact hdC
      refine ⟨l ++ [e], ?_, isStepPath_concat hl he hC, ?_⟩
      · rw [List.length_append, List.length_singleton]
        omega
      · rw [List.sum_append, List.sum_singleton, hsum, hae]

/-- The visited levels of a path: the prefix sum of `j` steps is reached in `j` steps. -/
theorem take_sum_mem_reachableExponents {x : X} {l : List ℤ} (hl : IsStepPath T C E x l) :
    ∀ j : ℕ, j ≤ l.length → (l.take j).sum ∈ reachableExponents T C E j x := by
  intro j
  induction j with
  | zero =>
    intro h0
    have hx : (T ^ (l.take 0).sum) x ∈ C := hl.1 0 h0
    rw [List.take_zero, List.sum_nil, zpow_zero, Homeomorph.one_apply] at hx
    rw [List.take_zero, List.sum_nil]
    exact zero_mem_reachableExponents hx
  | succ j ih =>
    intro hj
    have hjlt : j < l.length := by omega
    have hjle : j ≤ l.length := by omega
    have hmem : l[j] ∈ stepExponents E := hl.2 _ (List.getElem_mem hjlt)
    have hC : (T ^ (l.take (j + 1)).sum) x ∈ C := hl.1 (j + 1) hj
    rw [List.sum_take_succ l j hjlt] at hC ⊢
    exact mem_reachableExponents_succ.2 ⟨Or.inr ⟨(l.take j).sum, ih hjle, l[j], hmem, rfl⟩, hC⟩

/-- **Classes are endpoints of paths** (tex 1503–1505): `reachableExponents T C E r x` consists of
the endpoints of the paths from `x` of at most `r` steps. -/
theorem mem_reachableExponents_iff_path (r : ℕ) (x : X) (d : ℤ) :
    d ∈ reachableExponents T C E r x ↔
      ∃ l : List ℤ, l.length ≤ r ∧ IsStepPath T C E x l ∧ l.sum = d := by
  constructor
  · exact exists_path_of_mem_reachableExponents r
  · rintro ⟨l, hlen, hl, rfl⟩
    have h := take_sum_mem_reachableExponents hl l.length (Nat.le_refl _)
    rw [List.take_length] at h
    exact reachableExponents_mono hlen x h

/-- **Loop deletion**: if the prefix sums after `i` and after `j ≥ i` steps agree, the path returns
to the same point, and deleting the steps between them gives a path of `j - i` fewer steps with
the same endpoint. -/
theorem isStepPath_eraseSegment {x : X} {l : List ℤ} (hl : IsStepPath T C E x l) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ l.length) (heq : (l.take i).sum = (l.take j).sum) :
    IsStepPath T C E x (l.take i ++ l.drop j) ∧ (l.take i ++ l.drop j).sum = l.sum ∧
      (l.take i ++ l.drop j).length = l.length - (j - i) := by
  have hi : i ≤ l.length := Nat.le_trans hij hj
  have hleni : (l.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left hi]
  have hlen : (l.take i ++ l.drop j).length = l.length - (j - i) := by
    rw [List.length_append, hleni, List.length_drop]
    omega
  refine ⟨⟨fun k hk => ?_, fun e he => ?_⟩, ?_, hlen⟩
  · rw [hlen] at hk
    by_cases hki : k ≤ i
    · have hk' : k ≤ (l.take i).length := by
        rw [hleni]
        exact hki
      rw [List.take_append_of_le_length hk', List.take_take, Nat.min_eq_left hki]
      exact hl.1 k (Nat.le_trans hki hi)
    · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = i + t := ⟨k - i, by omega⟩
      have htake : (l.take i ++ l.drop j).take (i + t) = l.take i ++ (l.drop j).take t := by
        rw [List.take_append, List.take_take, Nat.min_eq_right (Nat.le_add_right i t), hleni,
          Nat.add_sub_cancel_left]
      have hjt : j + t ≤ l.length := by omega
      have h2 : (T ^ (l.take (j + t)).sum) x ∈ C := hl.1 (j + t) hjt
      rw [List.take_add, List.sum_append] at h2
      rw [htake, List.sum_append, heq]
      exact h2
  · rcases List.mem_append.1 he with h | h
    · exact hl.2 e (List.mem_of_mem_take h)
    · exact hl.2 e (List.mem_of_mem_drop h)
  · rw [List.sum_append, heq, List.sum_take_add_sum_drop]

/-- **Pigeonhole**: under the orbit bound, a path whose `length + 1` visited levels are distinct
has at most `m - 1` steps. -/
theorem length_le_of_injective (hm : ExponentBound T C m) {x : X} {l : List ℤ}
    (hl : IsStepPath T C E x l)
    (hinj : ∀ i ≤ l.length, ∀ j ≤ l.length, (l.take i).sum = (l.take j).sum → i = j) :
    l.length ≤ m - 1 := by
  have hcard : ((Finset.range (l.length + 1)).image fun k => (l.take k).sum).card =
      l.length + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have ha' := Finset.mem_range.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_range.1 (Finset.mem_coe.1 hb)
    exact hinj a (by omega) b (by omega) hab
  have hle := hm x ((Finset.range (l.length + 1)).image fun k => (l.take k).sum) fun n hn => by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hn
    have hk' := Finset.mem_range.1 hk
    exact hl.1 k (by omega)
  rw [hcard] at hle
  omega

/-- **Erasing loops** (tex 1504–1505): under the orbit bound, every path is replaced by a path of
at most `m - 1` steps with the same endpoint.  Strong induction on the length: a path with two
equal prefix sums loses the segment between them (`isStepPath_eraseSegment`); a path without
this has at most `m - 1` steps (`length_le_of_injective`). -/
theorem exists_short_path_of_path (hm : ExponentBound T C m) {x : X} {l : List ℤ}
    (hl : IsStepPath T C E x l) :
    ∃ l' : List ℤ, l'.length ≤ m - 1 ∧ IsStepPath T C E x l' ∧ l'.sum = l.sum := by
  have key : ∀ (n : ℕ) (p : List ℤ), p.length = n → IsStepPath T C E x p →
      ∃ l' : List ℤ, l'.length ≤ m - 1 ∧ IsStepPath T C E x l' ∧ l'.sum = p.sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro p hn hp
    by_cases hloop : ∃ i j : ℕ, i < j ∧ j ≤ p.length ∧ (p.take i).sum = (p.take j).sum
    · obtain ⟨i, j, hij, hj, heq⟩ := hloop
      obtain ⟨hp', hsum', hlen'⟩ := isStepPath_eraseSegment hp (Nat.le_of_lt hij) hj heq
      obtain ⟨q, hq, hpq, hsumq⟩ := ih (p.length - (j - i)) (by omega) _ hlen' hp'
      exact ⟨q, hq, hpq, hsumq.trans hsum'⟩
    · refine ⟨p, length_le_of_injective hm hp fun a ha b hb hab => ?_, hp, rfl⟩
      rcases lt_trichotomy a b with h | h | h
      · exact (hloop ⟨a, b, h, hb, hab⟩).elim
      · exact h
      · exact (hloop ⟨b, a, h, ha, hab.symm⟩).elim
  exact key l.length l rfl hl

/-- **Erasing loops, stage form**: the exponents reached from `x` in any number of steps are
reached in `m - 1` steps. -/
theorem reachableExponents_subset_of_exponentBound (hm : ExponentBound T C m) (r : ℕ) (x : X) :
    reachableExponents T C E r x ⊆ reachableExponents T C E (m - 1) x := by
  intro d hd
  obtain ⟨l, -, hl, rfl⟩ := (mem_reachableExponents_iff_path r x d).1 hd
  obtain ⟨l', hlen', hl', hsum'⟩ := exists_short_path_of_path hm hl
  exact (mem_reachableExponents_iff_path (m - 1) x l.sum).2 ⟨l', hlen', hl', hsum'⟩

end Paths

/-- **The printed sentence** (`non_mf_groups_exist.tex`, proof of `lem:transient-matrices`,
tex 1504–1505; census row `ff376e50f433`): "Erasing loops shortens any path between related points
to at most $m-1$ steps."  For partial shifts with exponents `E` (and their inverses) on `C`, where
each orbit meets `C` in at most `m` points, every path from `x` through `C` is replaced by a path
of at most `m - 1` steps from `x` to the same point. -/
def PrintedErasingLoopsSentence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (T : X ≃ₜ X) (C : Set X) (E : Finset ℤ) (m : ℕ),
    ExponentBound T C m → ∀ (x : X) (l : List ℤ), IsStepPath T C E x l →
      ∃ l' : List ℤ, l'.length ≤ m - 1 ∧ IsStepPath T C E x l' ∧ l'.sum = l.sum

/-- The printed sentence, proved. -/
theorem printedErasingLoopsSentence : PrintedErasingLoopsSentence.{u} :=
  fun _ _ _ _ _ _ hm _ _ hl => exists_short_path_of_path hm hl

end GroupApproximation.Full.NM18

#audit_axioms GroupApproximation.Full.NM18.mem_reachableExponents_iff_path
#audit_axioms GroupApproximation.Full.NM18.isStepPath_eraseSegment
#audit_axioms GroupApproximation.Full.NM18.length_le_of_injective
#audit_axioms GroupApproximation.Full.NM18.exists_short_path_of_path
#audit_axioms GroupApproximation.Full.NM18.reachableExponents_subset_of_exponentBound
#audit_closed_axioms GroupApproximation.Full.NM18.printedErasingLoopsSentence
