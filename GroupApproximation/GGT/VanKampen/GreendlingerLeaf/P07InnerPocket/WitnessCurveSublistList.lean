import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-36: sublists from local steps

Lane gl-p07-36.  List infrastructure for the reduction of
`FourPieceWitness.WitnessCurveSublistNondegStatement` (`FourBlockNondegStepStatement.lean`) to the
local step residual `FourPieceWitness.WitnessCurveStepStatement`
(`WitnessCurveSublistStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).
Certifies no printed sentence on its own.

* `CurveStep.StepNext w l x y`: in the word `w`, `x` comes before `y`, or `y` is the first entry
  of `w` that lies in `l`.
* `CurveStep.exists_split_sublist`: for duplicate-free `w` and `l` with `l ⊆ w`, if every
  consecutive pair of every rotation of `l` is a `StepNext` pair, then `l` is empty or some
  rotation `y :: (t ++ s)` of `l = s ++ y :: t` is a sublist of `w`.  The rotation starts at the
  first entry `y` of `w` in `l`; no pair of that rotation ends at `y`, so every pair is a forward
  step, and the forward steps chain to a sublist.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep

variable {α : Type*}

/-- **The step relation.**  In the word `w`, `x` comes before `y`, or `y` is the first entry of
`w` that lies in `l`. -/
def StepNext (w l : List α) (x y : α) : Prop :=
  (∃ u v z : List α, w = u ++ x :: (v ++ y :: z)) ∨
    ∃ u z : List α, w = u ++ y :: z ∧ ∀ t ∈ u, t ∉ l

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.StepNext

/-- A step relation for `l` is one for any list whose entries lie in `l`. -/
theorem StepNext.mono {w l m : List α} {x y : α} (hm : ∀ e ∈ m, e ∈ l)
    (h : StepNext w l x y) : StepNext w m x y := by
  rcases h with h | ⟨u, z, hw, hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, z, hw, fun t ht htm => hu t ht (hm t htm)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.StepNext.mono

/-- In a duplicate-free word, the position of an entry is unique. -/
theorem append_cons_inj_of_nodup {x : α} {u u' r r' : List α} (hw : (u ++ x :: r).Nodup)
    (h : u ++ x :: r = u' ++ x :: r') : u = u' ∧ r = r' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil =>
      simp only [List.nil_append] at h
      exact ⟨rfl, (List.cons_eq_cons.mp h).2⟩
    | cons c u' =>
      simp only [List.nil_append, List.cons_append] at h hw
      have hx : x ∈ r := by rw [(List.cons_eq_cons.mp h).2]; simp
      exact absurd hx (List.nodup_cons.mp hw).1
  | cons c u ih =>
    cases u' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h hw
      have hc : c ∈ u ++ x :: r := by rw [(List.cons_eq_cons.mp h).1]; simp
      exact absurd hc (List.nodup_cons.mp hw).1
    | cons c' u' =>
      simp only [List.cons_append] at h hw
      obtain ⟨hcc, h2⟩ := List.cons_eq_cons.mp h
      obtain ⟨hu, hr⟩ := ih (List.nodup_cons.mp hw).2 h2
      exact ⟨by rw [hcc, hu], hr⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.append_cons_inj_of_nodup

/-- A word that meets `l` has a first entry in `l`. -/
theorem exists_first_entry {l w : List α} (h : ∃ x ∈ l, x ∈ w) :
    ∃ u y z, w = u ++ y :: z ∧ y ∈ l ∧ ∀ t ∈ u, t ∉ l := by
  induction w with
  | nil =>
    obtain ⟨x, _, hx⟩ := h
    simp at hx
  | cons c w ih =>
    by_cases hc : c ∈ l
    · exact ⟨[], c, w, rfl, hc, fun t ht => by simp at ht⟩
    · obtain ⟨x, hxl, hx⟩ := h
      have hxw : x ∈ w := by
        rcases List.mem_cons.mp hx with h' | h'
        · subst h'
          exact absurd hxl hc
        · exact h'
      obtain ⟨u, y, z, hw, hy, hu⟩ := ih ⟨x, hxl, hxw⟩
      refine ⟨c :: u, y, z, by simp [hw], hy, fun t ht => ?_⟩
      rcases List.mem_cons.mp ht with h' | h'
      · rw [h']
        exact hc
      · exact hu t h'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.exists_first_entry

/-- The first entry of a word in `l` is unique. -/
theorem first_entry_unique {l z z' : List α} {y y' : α} {u u' : List α}
    (h : u ++ y :: z = u' ++ y' :: z') (hy : y ∈ l) (hy' : y' ∈ l)
    (hu : ∀ t ∈ u, t ∉ l) (hu' : ∀ t ∈ u', t ∉ l) : y = y' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil =>
      simp only [List.nil_append] at h
      exact (List.cons_eq_cons.mp h).1
    | cons c u' =>
      simp only [List.nil_append, List.cons_append] at h
      have hc : y = c := (List.cons_eq_cons.mp h).1
      exact absurd (hc ▸ hy) (hu' c (by simp))
  | cons c u ih =>
    cases u' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      have hc : c = y' := (List.cons_eq_cons.mp h).1
      exact absurd (hc ▸ hy') (hu c (by simp))
    | cons c' u' =>
      simp only [List.cons_append] at h
      exact ih (List.cons_eq_cons.mp h).2 (fun t ht => hu t (by simp [ht]))
        (fun t ht => hu' t (by simp [ht]))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.first_entry_unique

/-- **Forward steps chain to a sublist.**  If `y` sits in `w` before `z`, and every consecutive
pair of `y :: l` is a forward step of the duplicate-free word `w`, then `y :: l <+ y :: z`. -/
theorem sublist_of_forward {w : List α} (hw : w.Nodup) :
    ∀ {l : List α} {y : α} {u z : List α}, w = u ++ y :: z →
      (∀ (s t : List α) (x y' : α), y :: l = s ++ x :: y' :: t →
        ∃ u v z : List α, w = u ++ x :: (v ++ y' :: z)) →
      y :: l <+ y :: z := by
  intro l
  induction l with
  | nil => intro y u z _ _; exact List.cons_sublist_cons.mpr (List.nil_sublist _)
  | cons y' l ih =>
    intro y u z hwu hstep
    obtain ⟨u', v, z', hw'⟩ := hstep [] l y y' rfl
    have hwn : (u ++ y :: z).Nodup := hwu ▸ hw
    obtain ⟨_, hz⟩ := append_cons_inj_of_nodup hwn (hwu.symm.trans hw')
    have hw'' : w = (u' ++ y :: v) ++ y' :: z' := by rw [hw']; simp
    have hsub := ih hw'' (fun s t x y'' hst => hstep (y :: s) t x y'' (by rw [hst]; rfl))
    rw [hz]
    exact List.cons_sublist_cons.mpr (hsub.trans (List.sublist_append_right v _))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep.sublist_of_forward

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.CurveStep
