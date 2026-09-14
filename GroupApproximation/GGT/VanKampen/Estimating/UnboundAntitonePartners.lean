import Mathlib.Data.Nat.Find
import GroupApproximation.Meta.AxiomGuard

/-!
# Antitone partners on a backwards pair, and the split point (route B1 of GapSpan)

Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*, arXiv:math/0411039v3,
Appendix, proof of Lemma 9.4; route B1 of `OsinLemma94ClassCaseGapSpanStatement` (ct-bilateral-cell, item 10).
A backwards connector pair `a < a'` on the source word and `b' < b` on the target word is split at breakpoints of
the source.  This module is the combinatorial core, independent of the metric estimate:

* `latestPartner near a' b g`: the largest target index `h ≤ b` that is a partner (`near g'' h`) of some source index
  `g'' ∈ [g, a']`.  It is antitone in `g` (`latestPartner_antitone`) for any relation `near`, and it is a partner of
  some later source point (`exists_later_partner`).  The metric half bounds the distance from `g` to that later point.
* `exists_step_lt_of_lt`, `exists_positive_split`: along any breakpoints `g₀ < … < g_m` an antitone partner function
  that decreases strictly overall decreases strictly at some step: the split point with a strictly positive target
  arc.
* Model tests: `antiparallelPartners` (source `sⁿ`, target `(s⁻¹)ⁿ`, partner `n - g`) is antitone with the right
  endpoints, the latest partner recovers it, and a breakpoint list of it has a strict step.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open Classical in
/-- **The latest partner** of source index `g`: the largest `h ≤ b` partnered (`near g'' h`) with some source index
`g''` with `g ≤ g'' ≤ a'`, or `0` if there is none. -/
noncomputable def latestPartner (near : ℕ → ℕ → Prop) (a' b g : ℕ) : ℕ :=
  Nat.findGreatest (fun h => ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' h) b

theorem latestPartner_le (near : ℕ → ℕ → Prop) (a' b g : ℕ) : latestPartner near a' b g ≤ b := by
  classical
  exact Nat.findGreatest_le b

/-- **The latest partner is antitone** in the source index, for every partner relation. -/
theorem latestPartner_antitone (near : ℕ → ℕ → Prop) (a' b : ℕ) {g g' : ℕ} (hgg' : g ≤ g') :
    latestPartner near a' b g' ≤ latestPartner near a' b g := by
  classical
  unfold latestPartner
  exact Nat.findGreatest_mono
    (fun h ⟨g'', hg1, hg2, hnear⟩ => ⟨g'', le_trans hgg' hg1, hg2, hnear⟩) le_rfl

/-- A partner of `g` itself bounds the latest partner from below. -/
theorem le_latestPartner (near : ℕ → ℕ → Prop) {a' b g h : ℕ} (hga' : g ≤ a') (hhb : h ≤ b)
    (hnear : near g h) : h ≤ latestPartner near a' b g := by
  classical
  unfold latestPartner
  exact Nat.le_findGreatest hhb ⟨g, le_rfl, hga', hnear⟩

/-- **The latest partner is a partner of a later source point**, as soon as `g` has some partner `≤ b`. -/
theorem exists_later_partner (near : ℕ → ℕ → Prop) {a' b g h : ℕ} (hga' : g ≤ a') (hhb : h ≤ b)
    (hnear : near g h) :
    ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' (latestPartner near a' b g) := by
  classical
  unfold latestPartner
  exact Nat.findGreatest_spec (P := fun h => ∃ g'', g ≤ g'' ∧ g'' ≤ a' ∧ near g'' h) hhb
    ⟨g, le_rfl, hga', hnear⟩

/-- **The split point.**  A function that decreases strictly from index `0` to index `m` decreases strictly at some
step `i < m`. -/
theorem exists_step_lt_of_lt (f : ℕ → ℕ) : ∀ m : ℕ, f m < f 0 → ∃ i < m, f (i + 1) < f i
  | 0, h => absurd h (lt_irrefl _)
  | m + 1, h => by
      by_cases hs : f (m + 1) < f m
      · exact ⟨m, Nat.lt_succ_self m, hs⟩
      · obtain ⟨i, hi, hfi⟩ := exists_step_lt_of_lt f m (lt_of_le_of_lt (not_lt.mp hs) h)
        exact ⟨i, Nat.lt_succ_of_lt hi, hfi⟩

/-- **The split point along breakpoints**: for breakpoints `gs 0, …, gs m` and a partner function `h` with
`h (gs m) < h (gs 0)`, some consecutive pair of breakpoints has a strictly positive target arc. -/
theorem exists_positive_split (h gs : ℕ → ℕ) (m : ℕ) (hback : h (gs m) < h (gs 0)) :
    ∃ i < m, h (gs (i + 1)) < h (gs i) :=
  exists_step_lt_of_lt (fun i => h (gs i)) m hback

/-! ## Model tests -/

/-- The antiparallel model: source `sⁿ`, target `(s⁻¹)ⁿ` read from `sⁿ`, so the source vertex `g` is the target
vertex `n - g`.  The partner function is `g ↦ n - g`. -/
def antiparallelPartners (n : ℕ) (g : ℕ) : ℕ := n - g

theorem antiparallelPartners_antitone (n : ℕ) {g g' : ℕ} (h : g ≤ g') :
    antiparallelPartners n g' ≤ antiparallelPartners n g := by
  unfold antiparallelPartners
  omega

theorem antiparallelPartners_endpoints (n : ℕ) :
    antiparallelPartners n 0 = n ∧ antiparallelPartners n n = 0 := by
  unfold antiparallelPartners
  omega

/-- In the antiparallel model, the latest partner for "same vertex" is the antiparallel partner. -/
theorem latestPartner_antiparallel (n g : ℕ) (hg : g ≤ n) :
    latestPartner (fun g'' h => g'' + h = n) n n g = antiparallelPartners n g := by
  refine le_antisymm ?_ (le_latestPartner (fun g'' h => g'' + h = n) hg
    (show antiparallelPartners n g ≤ n by unfold antiparallelPartners; omega)
    (show g + antiparallelPartners n g = n by unfold antiparallelPartners; omega))
  obtain ⟨g'', hg1, hg2, hnear⟩ := exists_later_partner (fun g'' h => g'' + h = n) (a' := n) (b := n)
    hg (Nat.sub_le n g) (show g + (n - g) = n by omega)
  have hnear' : g'' + latestPartner (fun g'' h => g'' + h = n) n n g = n := hnear
  unfold antiparallelPartners
  omega

/-- Closed calibration: along the breakpoints `0, 2, 5, 7` of the antiparallel model at `n = 7`, there is a step with
a strictly positive target arc. -/
theorem antiparallel_split_model :
    ∃ i < 3, antiparallelPartners 7 ([0, 2, 5, 7].getD (i + 1) 0) <
      antiparallelPartners 7 ([0, 2, 5, 7].getD i 0) :=
  ⟨0, by decide, by decide⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

/-! ### Audit -/

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.latestPartner_antitone
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.le_latestPartner
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_later_partner
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_step_lt_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_positive_split
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.latestPartner_antiparallel
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.antiparallel_split_model
