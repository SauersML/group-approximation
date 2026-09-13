import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: cyclic runs of polygon sides

Osin (math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths".  `OsinLemma94ClassPolygons` reads the sides of a polygon cyclically from `classBase`
and splits them into runs of consecutive sides, the classes.  This module builds such runs for
any join predicate.

`J s` says that side `s` joins side `(s + 1) % n`.  If some side `s₀` does not join, read the
sides from `(s₀ + 1) % n` and cut after every side that does not join.  Each run is a block of
consecutive sides, every side of a run but the last joins the next one, the last one does not
join, and there are at most as many runs as sides that do not join.  If every side joins, there
is one run.

* `CyclicRuns.runs`: `(List.range n).rotate base`, cut after every side that does not join.
* `exists_cyclicRuns`: the run decomposition behind `OsinLemma94ClassPolygons`.
-/

namespace GroupApproximation.GGT.VanKampen

namespace CyclicRuns

/-- The runs of `(List.range n).rotate base`: the list cut after every side that does not
join. -/
abbrev runs (n base : ℕ) (J : ℕ → Prop) [DecidablePred J] : List (List ℕ) :=
  ((List.range n).rotate base).splitBy fun a _ => decide (J a)

/-- Reading the entries of a list of lists by index gives its flattening. -/
theorem flatMap_range_getD {α : Type*} (L : List (List α)) :
    (List.range L.length).flatMap (fun i => L.getD i []) = L.flatten := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      Nat.succ_eq_add_one, List.getD_cons_zero, List.getD_cons_succ, ih, List.flatten_cons]

/-- Consecutive entries of `(List.range n).rotate base` are consecutive mod `n`. -/
theorem isChain_rotate_range (n base : ℕ) :
    ((List.range n).rotate base).IsChain fun a b => b = (a + 1) % n := by
  rw [List.isChain_iff_getElem]
  intro t ht
  simp only [List.getElem_rotate, List.getElem_range, List.length_range]
  rw [Nat.mod_add_mod, show t + 1 + base = t + base + 1 by omega]

/-- Read from `(s + 1) % n`, the sides end with side `s`. -/
theorem getLast?_rotate_range {n s : ℕ} (hs : s < n) :
    ((List.range n).rotate ((s + 1) % n)).getLast? = some s := by
  have hne : (List.range n).rotate ((s + 1) % n) ≠ [] :=
    List.ne_nil_of_length_pos (by simp only [List.length_rotate, List.length_range]; omega)
  rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem hne, Option.some_inj]
  simp only [List.getElem_rotate, List.getElem_range, List.length_rotate, List.length_range]
  rcases Nat.lt_or_ge (s + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, show n - 1 + (s + 1) = s + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hs]
  · rw [show s + 1 = n by omega, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (show n - 1 < n by omega)]
    omega

/-- The runs, read in order, are the sides read from `base`. -/
theorem flatten_runs (n base : ℕ) (J : ℕ → Prop) [DecidablePred J] :
    (runs n base J).flatten = (List.range n).rotate base :=
  List.flatten_splitBy _ _

section Runs

variable {n base : ℕ} {J : ℕ → Prop} [DecidablePred J]

theorem getD_runs_eq {i : ℕ} (hi : i < (runs n base J).length) :
    (runs n base J).getD i [] = (runs n base J)[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Inside a run, every side joins the next one, and the next one is the next side mod `n`. -/
theorem getElem_of_mem_runs {m : List ℕ} (hm : m ∈ runs n base J) (t : ℕ)
    (ht : t + 1 < m.length) : m[t + 1] = (m[t] + 1) % n ∧ J m[t] := by
  have hinfix : m <:+: (List.range n).rotate base := by
    rw [← flatten_runs n base J]
    exact List.infix_of_mem_flatten hm
  exact ⟨List.isChain_iff_getElem.mp ((isChain_rotate_range n base).infix hinfix) t ht,
    of_decide_eq_true (List.isChain_iff_getElem.mp (List.isChain_of_mem_splitBy hm) t ht)⟩

/-- A run that is not the last one ends with a side that does not join. -/
theorem not_of_mem_getLast?_runs {i : ℕ} (hi : i + 1 < (runs n base J).length) {s : ℕ}
    (hs : s ∈ ((runs n base J)[i]'(by omega)).getLast?) : ¬ J s := by
  obtain ⟨ha, -, h⟩ :=
    List.isChain_iff_getElem.mp (List.isChain_getLast_head_splitBy _ _) i hi
  have hx : ((runs n base J)[i]'(by omega)).getLast ha = s :=
    Option.some_inj.mp ((List.getLast?_eq_some_getLast ha).symm.trans (Option.mem_def.mp hs))
  subst hx
  exact of_decide_eq_false h

/-- The last run ends with the last side read from `base`. -/
theorem getLast?_getElem_runs {i : ℕ} (hi : i + 1 = (runs n base J).length) :
    ((runs n base J)[i]'(by omega)).getLast? = ((List.range n).rotate base).getLast? := by
  have hl : (List.range n).rotate base ≠ [] := by
    intro h
    rw [runs, h, List.splitBy_nil, List.length_nil] at hi
    omega
  obtain rfl : i = (runs n base J).length - 1 := by omega
  have hg : runs n base J ≠ [] := List.splitBy_ne_nil.2 hl
  rw [← List.getLast_eq_getElem hg,
    List.getLast?_eq_some_getLast (List.ne_nil_of_mem_splitBy (List.getLast_mem hg)),
    List.getLast_getLast_splitBy (fun a _ => decide (J a)) hl, List.getLast?_eq_some_getLast hl]

end Runs

/-- Clauses one to three of `exists_cyclicRuns` for the runs read from any `base`. -/
theorem runs_spec (n base : ℕ) (J : ℕ → Prop) [DecidablePred J] :
    (List.range (runs n base J).length).flatMap (fun i => (runs n base J).getD i []) =
        (List.range n).rotate base ∧
      (∀ i < (runs n base J).length, (runs n base J).getD i [] ≠ []) ∧
      (∀ i < (runs n base J).length, ∀ t (ht : t + 1 < ((runs n base J).getD i []).length),
        ((runs n base J).getD i [])[t + 1] = (((runs n base J).getD i [])[t] + 1) % n ∧
          J ((runs n base J).getD i [])[t]) := by
  have hmem : ∀ i < (runs n base J).length, (runs n base J).getD i [] ∈ runs n base J := by
    intro i hi
    rw [getD_runs_eq hi]
    exact List.getElem_mem hi
  exact ⟨(flatMap_range_getD _).trans (flatten_runs n base J),
    fun i hi => List.ne_nil_of_mem_splitBy (hmem i hi),
    fun i hi t ht => getElem_of_mem_runs (hmem i hi) t ht⟩

end CyclicRuns

open CyclicRuns

/-- **The cyclic run decomposition behind `OsinLemma94ClassPolygons`.**  Osin
(math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths".  `J s` says that side `s` joins side `(s + 1) % n`.  Read from `base`, the sides
`0, …, n - 1` split into `count` nonempty runs of consecutive sides mod `n`.  Every side of a run
but the last joins the next one.  If some side does not join, every run ends with a side that
does not join, and there are at most as many runs as sides that do not join.  If every side
joins, there is at most one run. -/
theorem exists_cyclicRuns (n : ℕ) (J : ℕ → Prop) [DecidablePred J] :
    ∃ (count base : ℕ) (sides : ℕ → List ℕ),
      (List.range count).flatMap sides = (List.range n).rotate base ∧
      (∀ i < count, sides i ≠ []) ∧
      (∀ i < count, ∀ t (ht : t + 1 < (sides i).length),
        (sides i)[t + 1] = ((sides i)[t] + 1) % n ∧ J (sides i)[t]) ∧
      ((∃ s < n, ¬ J s) → ∀ i < count, ∀ s ∈ (sides i).getLast?, ¬ J s) ∧
      count ≤ max 1 ((Finset.range n).filter fun s => ¬ J s).card := by
  by_cases hex : ∃ s < n, ¬ J s
  · obtain ⟨s₀, hs₀, hJs₀⟩ := hex
    obtain ⟨h1, h2, h3⟩ := runs_spec n ((s₀ + 1) % n) J
    have h4 : ∀ i < (runs n ((s₀ + 1) % n) J).length,
        ∀ x ∈ ((runs n ((s₀ + 1) % n) J).getD i []).getLast?, ¬ J x := by
      intro i hi x hx
      rw [getD_runs_eq hi] at hx
      rcases Nat.lt_or_ge (i + 1) (runs n ((s₀ + 1) % n) J).length with hlt | hge
      · exact not_of_mem_getLast?_runs hlt hx
      · have hlast : i + 1 = (runs n ((s₀ + 1) % n) J).length := by omega
        rw [getLast?_getElem_runs hlast, getLast?_rotate_range hs₀, Option.mem_def,
          Option.some_inj] at hx
        subst hx
        exact hJs₀
    have hend : ∀ i (hi : i < (runs n ((s₀ + 1) % n) J).length),
        ((runs n ((s₀ + 1) % n) J).getD i []).getLastD 0 ∈ (runs n ((s₀ + 1) % n) J)[i] ∧
          ((runs n ((s₀ + 1) % n) J).getD i []).getLastD 0 ∈
            ((runs n ((s₀ + 1) % n) J).getD i []).getLast? := by
      intro i hi
      have hne := h2 i hi
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
      refine ⟨?_, Option.mem_def.mpr rfl⟩
      rw [← getD_runs_eq hi]
      exact List.getLast_mem hne
    have hmaps : Set.MapsTo (fun i => ((runs n ((s₀ + 1) % n) J).getD i []).getLastD 0)
        (Finset.range (runs n ((s₀ + 1) % n) J).length : Set ℕ)
        ((Finset.range n).filter fun s => ¬ J s : Set ℕ) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_range] at hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, h4 i hi _ (hend i hi).2⟩
      have hx := List.mem_flatten_of_mem (List.getElem_mem hi) (hend i hi).1
      rwa [flatten_runs n ((s₀ + 1) % n) J, List.mem_rotate, List.mem_range] at hx
    have hnodup : (runs n ((s₀ + 1) % n) J).flatten.Nodup := by
      rw [flatten_runs n ((s₀ + 1) % n) J]
      exact List.nodup_rotate.mpr List.nodup_range
    have hdisj := List.pairwise_iff_getElem.mp (List.nodup_flatten.mp hnodup).2
    have hinj : Set.InjOn (fun i => ((runs n ((s₀ + 1) % n) J).getD i []).getLastD 0)
        (Finset.range (runs n ((s₀ + 1) % n) J).length : Set ℕ) := by
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      dsimp only at hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hdisj i j hi hj hlt (hend i hi).1 (by rw [hij]; exact (hend j hj).1)
      · exact hdisj j i hj hi hlt (hend j hj).1 (by rw [← hij]; exact (hend i hi).1)
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_range] at hle
    exact ⟨(runs n ((s₀ + 1) % n) J).length, (s₀ + 1) % n,
      fun i => (runs n ((s₀ + 1) % n) J).getD i [], h1, h2, h3, fun _ => h4,
      le_trans hle (le_max_right _ _)⟩
  · have hall : ∀ s < n, J s := fun s hs => by
      by_contra hJ
      exact hex ⟨s, hs, hJ⟩
    obtain ⟨h1, h2, h3⟩ := runs_spec n 0 J
    refine ⟨(runs n 0 J).length, 0, fun i => (runs n 0 J).getD i [], h1, h2, h3,
      fun h => absurd h hex, le_trans ?_ (le_max_left _ _)⟩
    by_contra hgt
    have h0 : 0 < (runs n 0 J).length := by omega
    have hne : (runs n 0 J)[0] ≠ [] := List.ne_nil_of_mem_splitBy (List.getElem_mem h0)
    have hx := List.mem_flatten_of_mem (List.getElem_mem h0) (List.getLast_mem hne)
    rw [flatten_runs n 0 J, List.mem_rotate, List.mem_range] at hx
    exact not_of_mem_getLast?_runs (show 0 + 1 < (runs n 0 J).length by omega)
      (List.getLast_mem_getLast? hne) (hall _ hx)

#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.flatMap_range_getD
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.isChain_rotate_range
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.getLast?_rotate_range
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.flatten_runs
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.getD_runs_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.getElem_of_mem_runs
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.not_of_mem_getLast?_runs
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.getLast?_getElem_runs
#audit_axioms GroupApproximation.GGT.VanKampen.CyclicRuns.runs_spec
#audit_axioms GroupApproximation.GGT.VanKampen.exists_cyclicRuns

end GroupApproximation.GGT.VanKampen
