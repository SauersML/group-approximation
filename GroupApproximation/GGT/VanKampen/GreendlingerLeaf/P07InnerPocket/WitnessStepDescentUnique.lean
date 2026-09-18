import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: a step relation has at most one descent

Lane gl-p07-58.  Pure list combinatorics for the converse
`WitnessCurveSublistStepStatement → WitnessStepDescentStatement`.  Certifies no printed
sentence.  NOT COMPILED.

* `witnessStepDescent_rotate_of_mem_steps`: when `2 ≤ |l|`, every cyclic step `(x, y)` of `l`
  is a rotation step `l.rotate n = s ++ x :: y :: t`.
* `witnessStepDescent_turnSum_le_of_unique`: a duplicate-free list of steps with at most one
  descent turns at most once.
* `witnessStepDescent_first_of_descent`: a `StepNext` step that is a descent ends at the
  `w`-first entry of `l`.  Two such entries coincide (`witnessStepDescent_eq_of_first`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

section DescentUnique

variable {α : Type*}

/-- The steps of `a :: r` closed by `c`: either the closing step, or an inner step. -/
theorem witnessStepDescent_zip_cases {x y c : α} (r : List α) : ∀ (a : α),
    (x, y) ∈ List.zip (a :: r) (r ++ [c]) →
      (∃ u, a :: r = u ++ [x] ∧ y = c) ∨ ∃ s t, a :: r = s ++ x :: y :: t := by
  induction r with
  | nil =>
    intro a h
    simp only [List.nil_append, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨hxa, hyc⟩ := Prod.mk.inj h
      exact Or.inl ⟨[], by rw [hxa, List.nil_append], hyc⟩
    · exact absurd h (by simp)
  | cons b r ih =>
    intro a h
    rw [List.cons_append, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨hxa, hyb⟩ := Prod.mk.inj h
      exact Or.inr ⟨[], r, by rw [hxa, hyb, List.nil_append]⟩
    · rcases ih b h with ⟨u, hu, hyc⟩ | ⟨s, t, hst⟩
      · exact Or.inl ⟨a :: u, by rw [hu, List.cons_append], hyc⟩
      · exact Or.inr ⟨a :: s, t, by rw [hst, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_zip_cases

/-- **A cyclic step of a list of length at least two is a rotation step.** -/
theorem witnessStepDescent_rotate_of_mem_steps {l : List α} {x y : α} (hl : 2 ≤ l.length)
    (h : (x, y) ∈ witnessStepDescent_steps l) :
    ∃ (n : ℕ) (s t : List α), l.rotate n = s ++ x :: y :: t := by
  cases l with
  | nil => exact absurd hl (by simp)
  | cons a r =>
    have hrot : (a :: r).rotate 1 = r ++ [a] := by simp
    unfold witnessStepDescent_steps at h
    rw [hrot] at h
    rw [List.length_cons] at hl
    rcases witnessStepDescent_zip_cases r a h with ⟨u, hu, hya⟩ | ⟨s, t, hst⟩
    · cases u with
      | nil =>
        have h1 := congrArg List.length hu
        rw [List.length_cons, List.nil_append, List.length_singleton] at h1
        omega
      | cons c u =>
        have hac : a = c := (List.cons.inj (hu.trans List.cons_append)).1
        refine ⟨(c :: u).length, [], u, ?_⟩
        rw [hu, List.rotate_append_length_eq, hya, hac, List.singleton_append,
          List.nil_append]
    · exact ⟨0, s, t, by rw [List.rotate_zero]; exact hst⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_rotate_of_mem_steps

/-- A list of steps without descents does not turn. -/
theorem witnessStepDescent_turnSum_eq_zero {f : α → ℕ} {N : ℕ} (ps : List (α × α))
    (h : ∀ p ∈ ps, f p.1 < f p.2) : witnessStepDescent_turnSum f N ps = 0 := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    have ht : witnessStepDescent_turn f N q = 0 := if_pos (h q List.mem_cons_self)
    rw [witnessStepDescent_turnSum_cons, ih (fun p hp => h p (List.mem_cons_of_mem q hp)), ht]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum_eq_zero

/-- **At most one descent turns at most once** (for a duplicate-free list of steps). -/
theorem witnessStepDescent_turnSum_le_of_unique {f : α → ℕ} {N : ℕ} (ps : List (α × α))
    (hnd : ps.Nodup)
    (h : ∀ p ∈ ps, ∀ q ∈ ps, ¬ f p.1 < f p.2 → ¬ f q.1 < f q.2 → p = q) :
    witnessStepDescent_turnSum f N ps ≤ N := by
  induction ps with
  | nil => exact Nat.zero_le N
  | cons q ps ih =>
    rw [witnessStepDescent_turnSum_cons]
    have hq : q ∉ ps := (List.nodup_cons.mp hnd).1
    by_cases hd : f q.1 < f q.2
    · have ht : witnessStepDescent_turn f N q = 0 := if_pos hd
      have := ih (List.nodup_cons.mp hnd).2 (fun p hp r hr =>
        h p (List.mem_cons_of_mem q hp) r (List.mem_cons_of_mem q hr))
      omega
    · have ht : witnessStepDescent_turn f N q = N := if_neg hd
      have h0 : witnessStepDescent_turnSum f N ps = 0 := by
        refine witnessStepDescent_turnSum_eq_zero ps fun p hp => ?_
        by_contra hp'
        have hpq := h p (List.mem_cons_of_mem q hp) q List.mem_cons_self hp' hd
        rw [hpq] at hp
        exact hq hp
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum_le_of_unique

/-- **A `StepNext` step that is a descent ends at the `w`-first entry of `l`.**  The in-order
alternative `w = u ++ x :: (v ++ y :: z)` puts `y` strictly after `x`, so it is not a descent. -/
theorem witnessStepDescent_first_of_descent {w l : List α} {x y : α} (hw : w.Nodup)
    (hs : WitnessCurveSublistList.StepNext w l x y)
    (hd : ¬ witnessStepDescent_pos x w < witnessStepDescent_pos y w) :
    ∃ u z : List α, w = u ++ y :: z ∧ ∀ t ∈ u, t ∉ l := by
  rcases hs with ⟨u, v, z, h1⟩ | h2
  · exfalso
    have hw1 := hw
    rw [h1] at hw1
    have hxu : x ∉ u := fun hx =>
      (List.nodup_append.mp hw1).2.2 x hx x List.mem_cons_self rfl
    have e1 : witnessStepDescent_pos x w = u.length := by
      rw [h1]
      exact witnessStepDescent_pos_split hxu
    have hw2 : w = (u ++ x :: v) ++ y :: z := by simp [h1]
    have hw3 := hw
    rw [hw2] at hw3
    have hyu : y ∉ u ++ x :: v := fun hy =>
      (List.nodup_append.mp hw3).2.2 y hy y List.mem_cons_self rfl
    have e2 : (u ++ x :: v).length ≤ witnessStepDescent_pos y w := by
      rw [hw2]
      exact witnessStepDescent_length_le_pos hyu
    rw [List.length_append, List.length_cons] at e2
    omega
  · exact h2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_first_of_descent

/-- **Two `w`-first entries of `l` coincide.** -/
theorem witnessStepDescent_eq_of_first {w l u z u' z' : List α} {y y' : α}
    (h : w = u ++ y :: z) (hu : ∀ t ∈ u, t ∉ l) (h' : w = u' ++ y' :: z')
    (hu' : ∀ t ∈ u', t ∉ l) (hy : y ∈ l) (hy' : y' ∈ l) : y = y' := by
  have hyu : y ∉ u := fun hm => hu y hm hy
  have hyu' : y ∉ u' := fun hm => hu' y hm hy
  have hy'u : y' ∉ u := fun hm => hu y' hm hy'
  have hy'u' : y' ∉ u' := fun hm => hu' y' hm hy'
  have e1 : witnessStepDescent_pos y w = u.length := by
    rw [h]
    exact witnessStepDescent_pos_split hyu
  have e2 : witnessStepDescent_pos y' w = u'.length := by
    rw [h']
    exact witnessStepDescent_pos_split hy'u'
  have e3 : u.length ≤ witnessStepDescent_pos y' w := by
    rw [h]
    exact witnessStepDescent_length_le_pos hy'u
  have e4 : u'.length ≤ witnessStepDescent_pos y w := by
    rw [h']
    exact witnessStepDescent_length_le_pos hyu'
  have hlen : u.length = u'.length := by omega
  exact (List.cons.inj (List.append_inj (h.symm.trans h') hlen).2).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_eq_of_first

/-- Two members of a list of length at most one coincide. -/
theorem witnessStepDescent_eq_of_length_le_one {β : Type*} {L : List β} {p q : β}
    (hL : L.length ≤ 1) (hp : p ∈ L) (hq : q ∈ L) : p = q := by
  cases L with
  | nil => exact absurd hp List.not_mem_nil
  | cons a r =>
    cases r with
    | nil =>
      rw [List.mem_singleton] at hp hq
      exact hp.trans hq.symm
    | cons _ _ =>
      rw [List.length_cons, List.length_cons] at hL
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_eq_of_length_le_one

/-- The second components of the cyclic steps are the rotation by one. -/
theorem witnessStepDescent_map_snd_steps (l : List α) :
    (witnessStepDescent_steps l).map Prod.snd = l.rotate 1 := by
  unfold witnessStepDescent_steps
  exact List.map_snd_zip (List.length_rotate l 1).le

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_map_snd_steps

/-- The cyclic steps of a duplicate-free list are duplicate free. -/
theorem witnessStepDescent_steps_nodup {l : List α} (hl : l.Nodup) :
    (witnessStepDescent_steps l).Nodup := by
  apply List.Nodup.of_map Prod.snd
  rw [witnessStepDescent_map_snd_steps]
  exact List.nodup_rotate.mpr hl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_steps_nodup

/-- Cyclic steps of a duplicate-free list with the same end are equal. -/
theorem witnessStepDescent_eq_of_snd {l : List α} (hl : l.Nodup) {p q : α × α}
    (hp : p ∈ witnessStepDescent_steps l) (hq : q ∈ witnessStepDescent_steps l)
    (h : p.2 = q.2) : p = q := by
  have hnd : ((witnessStepDescent_steps l).map Prod.snd).Nodup := by
    rw [witnessStepDescent_map_snd_steps]
    exact List.nodup_rotate.mpr hl
  exact List.inj_on_of_nodup_map hnd hp hq h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_eq_of_snd

/-- The end of a cyclic step lies in the list. -/
theorem witnessStepDescent_snd_mem {l : List α} {p : α × α}
    (hp : p ∈ witnessStepDescent_steps l) : p.2 ∈ l := by
  have h1 : p.2 ∈ (witnessStepDescent_steps l).map Prod.snd := List.mem_map_of_mem hp
  rw [witnessStepDescent_map_snd_steps] at h1
  exact (List.mem_rotate (n := 1)).mp h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_snd_mem

/-- **Every `StepNext` step gives the winding-one bound.**  Every descent of `l` against `w`
ends at the `w`-first entry of `l`, so by injectivity of the step ends there is at most one
descent, and the telescoped gap sum is at most `|w|`. -/
theorem witnessStepDescent_bound_of_steps {w l : List α} (hw : w.Nodup) (hl : l.Nodup)
    (hstep : ∀ (n : ℕ) (s t : List α) (x y : α), l.rotate n = s ++ x :: y :: t →
      WitnessCurveSublistList.StepNext w l x y) :
    witnessStepDescent_gapSum (fun e => witnessStepDescent_pos e w) w.length
      (witnessStepDescent_steps l) ≤ w.length := by
  rw [witnessStepDescent_gapSum_steps (fun e => witnessStepDescent_pos e w) w.length l
    (fun e => witnessStepDescent_pos_le_length e w)]
  refine witnessStepDescent_turnSum_le_of_unique _ (witnessStepDescent_steps_nodup hl) ?_
  intro p hp q hq hdp hdq
  by_cases hlen : 2 ≤ l.length
  · have hfst : ∀ r ∈ witnessStepDescent_steps l,
        ¬ witnessStepDescent_pos r.1 w < witnessStepDescent_pos r.2 w →
        ∃ u z : List α, w = u ++ r.2 :: z ∧ ∀ t ∈ u, t ∉ l := by
      rintro ⟨x, y⟩ hr hdr
      obtain ⟨n, s, t, hrot⟩ := witnessStepDescent_rotate_of_mem_steps hlen hr
      exact witnessStepDescent_first_of_descent hw (hstep n s t x y hrot) hdr
    obtain ⟨_, _, hu, hul⟩ := hfst p hp hdp
    obtain ⟨_, _, hu', hul'⟩ := hfst q hq hdq
    exact witnessStepDescent_eq_of_snd hl hp hq
      (witnessStepDescent_eq_of_first hu hul hu' hul' (witnessStepDescent_snd_mem hp)
        (witnessStepDescent_snd_mem hq))
  · have hs : (witnessStepDescent_steps l).length ≤ 1 := by
      unfold witnessStepDescent_steps
      rw [List.length_zip, List.length_rotate]
      omega
    exact witnessStepDescent_eq_of_length_le_one hs hp hq

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_bound_of_steps

end DescentUnique

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
